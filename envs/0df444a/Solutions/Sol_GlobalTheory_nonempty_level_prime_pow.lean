-- Prove2me | solution 1 for GlobalTheory.nonempty_level_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:05.165799+00:00
-- url     : https://prove2.me/submissions/fa427629-8e7c-4e85-af6c-20a5814afb72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsIsSymplecticFamilySpan
import Theorems.Thm_GlobalTheory_LevelExist_exists_stdSymp_of_pairing
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_symm
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (n J : ℕ), n.Prime → (n : K) ≠ 0 →
    ∀ ze : Γ(Spec (CommRingCat.of K), ⊤)ˣ, IsPrimitiveRoot ze (n ^ J) → Nonempty (Level P (n ^ J) ze) := by
  intro hL K _ _ P n J hn hK ze hz
  have := P.isAb.comm
  have : IsDomain Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have hcard : ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
      (m : ℕ), Nat.card {x : Over.mk s ⟶ P.A // x ^ n ^ m = 1} = (n ^ m) ^ (2 * P.g) := fun K' _ _ s m =>
    (hL.mulN _ P (n ^ m) (Nat.one_le_pow _ _ hn.pos)).2.2.2.2 K' s (by
      rw [Nat.cast_pow, ← map_natCast (Spec.preimage s).hom]
      exact pow_ne_zero _ ((map_ne_zero _).2 hK))
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P (n ^ J) (baseOver _)
  obtain ⟨v, hv, hw, hinj⟩ := LevelExist.exists_stdSymp_of_pairing (G := baseOver _ ⟶ P.A) (g := P.g) hn
    (hcard K (𝟙 _)) hz (fun x y c => WeilIs P.A P.L (n ^ J : ℕ) x y c) w₁ w₂ w₃
    (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h)
    (hL.weilNondeg K P _ (by rw [Nat.cast_pow]; exact pow_ne_zero _ hK))
  have hind : ∀ (K' : Type) [Field K'] (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K)),
      Function.Injective fun c : Fin (2 * P.g) → Fin (n ^ J) => linComb (fun i =>
        (Over.homMk s (by simp) : Over.mk s ⟶ baseOver _) ≫ v i) (fun i => (c i : ℕ)) := by
    intro K' _ s c c' h
    have : Surjective s := ⟨fun z => ⟨(default : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    have : Epi s := Flat.epi_of_flat_of_surjective s
    let b : Over.mk s ⟶ baseOver _ := Over.homMk s (by simp)
    let φ : (baseOver _ ⟶ P.A) →* (Over.mk s ⟶ P.A) := MonoidHom.mk' (b ≫ ·) fun _ _ => MonObj.comp_mul _ _ _
    have e : ∀ c : Fin (2 * P.g) → Fin (n ^ J),
        linComb (fun i => b ≫ v i) (fun i => (c i : ℕ)) = φ (∏ i, v i ^ (c i : ℕ)) := fun c => by
      rw [linComb, List.prod_ofFn, map_prod]
      simp only [map_pow]
      rfl
    have h' := (e c).symm.trans (h.trans (e c'))
    exact hinj (Over.OverMorphism.ext ((cancel_epi s).1 (congrArg (fun q => q.left) h')))
  refine ⟨⟨v, hz, hv, fun K' _ _ s => hind K' s, fun K' _ _ s y hy => ?_, hw⟩⟩
  let F : (Fin (2 * P.g) → Fin (n ^ J)) → {x : Over.mk s ⟶ P.A // x ^ n ^ J = 1} := fun c =>
    ⟨linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver _) ≫ v i) (fun i => (c i : ℕ)), by
      rw [linComb, List.prod_ofFn, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [← pow_mul, Nat.mul_comm, pow_mul, ← MonObj.comp_pow, hv, MonObj.comp_one, one_pow]⟩
  have : Finite {x : Over.mk s ⟶ P.A // x ^ n ^ J = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; have := hn.pos; positivity)
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun c c' h => hind K' s (congrArg Subtype.val h), by rw [hcard]; simp⟩
  obtain ⟨c, hc⟩ := hF.2 ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc⟩
end GlobalTheory
