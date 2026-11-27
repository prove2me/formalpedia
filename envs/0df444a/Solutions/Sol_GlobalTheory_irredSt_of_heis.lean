-- Prove2me | solution 1 for GlobalTheory.irredSt_of_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:15.185416+00:00
-- url     : https://prove2.me/submissions/6bd517fe-7fca-4c4b-8e42-bd51fbe68626

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsFieldGlobalFnsSpec
import Theorems.Thm_GlobalTheory_heis_irred_of_isField
import Theorems.Thm_GlobalTheory_isField_globalFns_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → (∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤) → WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → WeilNondegSt → MulNSt → GlobalSectionsRankAlgClosed → IrredSt := by
  intro hρ hWC hH hW hW3 hND hM hH0 K _ _ P k hk hkK W hstab
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ρ, hact, hcomm, -, -⟩ := hρ _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨hwc, hlift⟩ := hWC _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨hex, hmul, -, -⟩ := hW _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨-, hskew, -⟩ := hW3 _ P k (baseOver (Spec (CommRingCat.of K)))
  have hsub : Subsingleton (baseOver (Spec (CommRingCat.of K))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let G : Subgroup (baseOver (Spec (CommRingCat.of K)) ⟶ P.A) := (powMonoidHom k).ker
  have hG : ∀ x : G, x.1 ^ k = 1 := fun x => x.2
  have hcard : Nat.card G = k ^ (2 * P.g) :=
    (hM _ P k hk1).2.2.2.2 K (𝟙 _) hkK
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  choose θ hθ using fun x : G => hlift x.1 (hG x) hsub
  choose c hc hcu using fun x y : G => hex x.1 y.1 (hG x) (hG y)
  have hcmul : ∀ x x' y : G, c (x * x') y = c x y * c x' y := fun x x' y =>
    (hcu (x * x') y _ (hmul _ _ _ _ _ (hc x y) (hc x' y))).symm
  have hcskew : ∀ x y : G, c y x = (c x y)⁻¹ := fun x y =>
    (hcu y x _ (hskew _ _ _ (hc x y))).symm
  let e : G → G →* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ := fun x =>
    MonoidHom.mk' (fun y => c x y) (fun y y' => by
      rw [hcskew (y * y') x, hcmul, hcskew y x, hcskew y' x, mul_inv])
  have hfr := hH0 K P k hk1
  refine heis_irred_of_isField hH _ G _ (isField_globalFns_spec K)
    (by rw [hfr]; positivity) (fun x => ρ (θ x)) e ?_ ?_ ?_ W ?_
  · intro x y v
    refine hcomm _ _ _ ((hwc _ _ _).1 ?_) v
    rw [(hθ x).1, (hθ y).1]
    exact hc x y
  · intro x x' hxx
    have hone : ∀ y : G, c 1 y = 1 := fun y => by
      have := hcmul 1 1 y
      rw [_root_.mul_one] at this
      exact left_eq_mul.1 this
    have h : (x * x'⁻¹).1 = 1 := by
      refine hND K P k hkK _ (hG _) fun y hy => ?_
      have h1 : c x ⟨y, hy⟩ = c x' ⟨y, hy⟩ := DFunLike.congr_fun hxx ⟨y, hy⟩
      have h2 : c (x * x'⁻¹) ⟨y, hy⟩ = 1 := by
        rw [hcmul, h1, ← hcmul, mul_inv_cancel, hone]
      have := hc (x * x'⁻¹) ⟨y, hy⟩
      rwa [h2] at this
    exact mul_inv_eq_one.1 (Subtype.ext h)
  · rw [hfr, hcard, ← pow_mul, mul_comm]
  · intro x v hv
    exact hstab (θ x) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (θ x) v)) ((hact _ _ _).2 rfl) hv
end GlobalTheory
