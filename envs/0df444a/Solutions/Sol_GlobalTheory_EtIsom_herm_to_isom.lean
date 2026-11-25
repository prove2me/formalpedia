-- Prove2me | solution 1 for GlobalTheory.EtIsom.herm_to_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:30.537731+00:00
-- url     : https://prove2.me/submissions/7d6a2ddb-0406-47bb-aae7-8b29033ef5e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_rec_eq
import Theorems.Thm_GlobalTheory_EtIsom_pow_rec
import Theorems.Thm_GlobalTheory_EtIsom_bL_apply
import Theorems.Thm_GlobalTheory_EtIsom_mat_rec
import Theorems.Thm_GlobalTheory_EtIsom_form_eq
import Theorems.Thm_GlobalTheory_EtIsom_cayley_hasInv
import Theorems.Thm_GlobalTheory_EtIsom_mom_all
import Theorems.Thm_GlobalTheory_EtIsom_vec_li
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.EtIsom
theorem _root_.solution (hG : A.IsGen τ p) {lam : F} {a : A.K} (ha : IsUnit a) {X : Hn r F E}
    (hX : HasInv X (A.invK τ p lam a)) (x : A.K) (y : A.L) (hy : IsUnit y) (hxa : a = x * A.NL y) :
    ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧
      j y = X.2.1 := by
  have hAh : X.1.1.conjTranspose = X.1.1 := by rw [← Matrix.star_eq_conjTranspose]; exact X.1.2
  let bv : Module.Basis (Fin r) E (Fin r → E) :=
    basisOfLinearIndependentOfCardEqFinrank' _ (vec_li A hG ha hX) (by simp)
  have hbv : ∀ i, bv i = X.1.1 ^ (i : ℕ) *ᵥ X.2.1 := fun i => by
    simp [bv, coe_basisOfLinearIndependentOfCardEqFinrank']
  let φ : A.L ≃ₗ[E] (Fin r → E) := (bL A hG).equiv bv (Equiv.refl _)
  have hφb : ∀ i, φ (bL A hG i) = X.1.1 ^ (i : ℕ) *ᵥ X.2.1 := fun i => by
    simp [φ, Module.Basis.equiv_apply, hbv]
  have hφ : ∀ n : ℕ, φ (algebraMap A.K A.L (τ ^ n)) = X.1.1 ^ n *ᵥ X.2.1 := by
    refine rec_eq (fun i => algebraMap F E (p i)) (fun n => φ (algebraMap A.K A.L (τ ^ n)))
      (fun n => X.1.1 ^ n *ᵥ X.2.1) (fun m => ?_) (mat_rec _ _ (cayley_hasInv A hX) _) (fun n hn => ?_)
    · show φ (algebraMap A.K A.L (τ ^ (m + r))) =
        -∑ i, algebraMap F E (p i) • φ (algebraMap A.K A.L (τ ^ (m + (i : ℕ))))
      rw [pow_rec A hG, map_neg, map_sum, map_neg, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← IsScalarTower.algebraMap_apply F A.K A.L, IsScalarTower.algebraMap_apply F E A.L,
        ← Algebra.smul_def, map_smul]
    · have := hφb ⟨n, hn⟩
      rwa [bL_apply] at this
  have hτ : ∀ w, φ (algebraMap A.K A.L τ * w) = X.1.1 *ᵥ φ w := by
    have h : (φ.toLinearMap ∘ₗ LinearMap.mulLeft E (algebraMap A.K A.L τ)) =
        (Matrix.toLin' X.1.1) ∘ₗ φ.toLinearMap := by
      refine (bL A hG).ext fun i => ?_
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply,
        bL_apply]
      rw [← map_mul, ← pow_succ', hφ, hφ, Matrix.mulVec_mulVec, pow_succ']
    intro w
    exact LinearMap.congr_fun h w
  let u := hy.unit
  have h1 : y * ((u⁻¹ : A.Lˣ) : A.L) = 1 := hy.mul_val_inv
  have h2 : star y * star ((u⁻¹ : A.Lˣ) : A.L) = 1 := by rw [← star_mul', h1, star_one]
  let mE : A.L ≃ₗ[E] A.L := LinearEquiv.ofLinear (LinearMap.mulRight E ((u⁻¹ : A.Lˣ) : A.L))
    (LinearMap.mulRight E (u : A.L)) (by ext z; simp [mul_assoc]) (by ext z; simp [mul_assoc])
  have hj : ∀ z, (mE.trans φ) z = φ (z * ((u⁻¹ : A.Lˣ) : A.L)) := fun z => rfl
  refine ⟨mE.trans φ, fun z z' => ?_, fun z => ?_, ?_⟩
  · rw [hj, hj]
    refine (form_eq A hG a X.1.1 hAh X.2.1 (mom_all A hG hX) φ.toLinearMap hφb _ _).trans ?_
    congr 1
    rw [hxa, map_mul, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1 y, star_mul']
    linear_combination (algebraMap A.K A.L x * star z * z') * (star y * star ((u⁻¹ : A.Lˣ) : A.L)) * h1 +
      (algebraMap A.K A.L x * star z * z') * h2
  · rw [hj, hj, mul_assoc, hτ]
  · rw [hj, h1, ← map_one (algebraMap A.K A.L), ← pow_zero τ, hφ, pow_zero, Matrix.one_mulVec]
end GlobalTheory.EtIsom
