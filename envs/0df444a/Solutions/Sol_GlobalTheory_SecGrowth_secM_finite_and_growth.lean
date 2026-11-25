-- Prove2me | solution 1 for GlobalTheory.SecGrowth.secM_finite_and_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:14.815158+00:00
-- url     : https://prove2.me/submissions/b87c30f5-0f65-4672-9b79-4b49a04b677e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent
import Theorems.Thm_GlobalTheory_SecGrowth_growth_of_veryAmpleBy
import Theorems.Thm_GlobalTheory_SecGrowth_finrank_compHom
import Theorems.Thm_GlobalTheory_SecGrowth_finite_compHom
import Theorems.Thm_GlobalTheory_SecGrowth_finite_secM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
namespace GlobalTheory.SecGrowth
theorem _root_.solution :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F) → (∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] (m g : ℕ) (r : Fin m → B), Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B) → Algebra.trdeg K B = g → ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ∧ Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g) → (∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X), IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (∀ j : ℕ, Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) ∧ ∃ N c C : ℕ, 1 ≤ N ∧ 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ P.g ≤ c * Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ∧ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ≤ C * t ^ P.g := by
  intro hGI hProj hFin hGen hGK hTr K _ _ P
  have hfin := finite_secM P (hFin K P)
  refine ⟨fun j => hfin j, ?_⟩
  let T : Over (Spec (CommRingCat.of K)) := baseOver (Spec (CommRingCat.of K))
  let π : (T ⊗ P.A).left ⟶ P.A.left := (snd T P.A).left
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst T P.A).left
  have hpb : IsPullback π f P.A.hom (𝟙 _) := (IsPullback.of_hasPullback T.hom P.A.hom).flip
  obtain ⟨N, hN, m, s, hH, hs⟩ := hProj _ P K (𝟙 _) _ π f hpb
  obtain ⟨t₀, ht₀⟩ := hGen K _ f _ m s hH hs
  have hgi := hGI _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected
  haveI : IsIntegral (T ⊗ P.A).left := GeometricallyIntegral.geometrically_isIntegral _ _ _ hpb
  have hsm : SmoothOfRelativeDimension P.g f :=
    (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback hpb P.smoothDim
  let e : K ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  let V : ℕ → Type := fun t => SecM P.A P.L ((N * t : ℕ) : ℤ) T
  letI : ∀ t, Module K (V t) := fun t => Module.compHom (V t) e.toRingHom
  haveI : ∀ t, Module.Finite K (V t) := fun t => finite_compHom e
  have hrk : ∀ t, Module.finrank K (V t) = Module.finrank Γ(T.left, ⊤) (V t) := fun t => finrank_compHom e
  obtain ⟨c, C, hc, hcC⟩ := growth_of_veryAmpleBy f s hs P.g t₀ ht₀ (fun B _ _ _ r => hGK K B _ _ r)
    (hTr K _ f P.g hsm) V (fun t v => toPw P.L π N t (SecM.toSec P.A v))
    (fun t a b k => map_add (rs _ (wchart_le_one P.L π k)) _ _)
    (fun t c a k => (map_mul (rs _ (wchart_le_one P.L π k)) (cst f _ c) _).trans
      (congrArg₂ (· * ·) (rs_cst f _ c) rfl))
    (fun t a ha => by
      refine Subtype.ext (funext fun j => ?_)
      obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
      have h := congrArg (rs _ (wchart_le_unit P.L π (fun _ => k))) (ha fun _ => k)
      exact ((rs_rs _ _ _).trans (rs_self _ _)).symm.trans (h.trans (map_zero _)))
    (fun t σ => ⟨SecM.ofSec P.A (ofPw P.L π N t σ), fun k => (rs_rs _ _ _).trans (rs_self _ _)⟩)
  refine ⟨N, c, C, hN, hc, fun t ht => ?_⟩
  have h := hcC t ht
  rw [hrk] at h
  exact h
end GlobalTheory.SecGrowth
