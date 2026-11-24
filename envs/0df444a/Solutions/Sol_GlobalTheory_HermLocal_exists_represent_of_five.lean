-- Prove2me | solution 1 for GlobalTheory.HermLocal.exists_represent_of_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:18:44.665384+00:00
-- url     : https://prove2.me/submissions/46a679c4-d1b2-4b40-b2c3-fdfc652eb75d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_GlobalTheory_HermLocal_exists_zero_coord
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_of_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermLocal
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {c : L →+* L}
namespace GlobalTheory.HermLocal
theorem _root_.solution (h2 : (2 : K) ≠ 0)
    (H : ∀ a : Fin 5 → K, ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0)
    (hF : ∀ t : L, c t = t ↔ ∃ s : K, algebraMap K L s = t) {θ : L} (h0 : θ ≠ 0) (hθ : c θ = -θ)
    {r : ℕ} (hr : 2 ≤ r) {g : Fin r → L}
    (hg : ∀ i, c (g i) = g i) (hg0 : ∀ i, g i ≠ 0) {b : L} (hb : c b = b) (hb0 : b ≠ 0) :
    ∃ z : Fin r → L, z ⬝ᵥ Matrix.diagonal g *ᵥ (c ∘ z) = b := by
  obtain ⟨d, hd⟩ := (hF (θ * θ)).1 (by rw [map_mul, hθ]; ring)
  choose γ hγ' using fun i => (hF (g i)).1 (hg i)
  obtain ⟨κ, hκ'⟩ := (hF b).1 hb
  have hγ : ∀ i, γ i ≠ 0 := fun i h => hg0 i (by rw [← hγ', h, map_zero])
  have hκ : κ ≠ 0 := fun h => hb0 (by rw [← hκ', h, map_zero])
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (by rw [← hd, h, map_zero])
  let a : Option (Fin r ⊕ Fin r) → K := fun o => o.elim (-κ) (Sum.elim γ fun i => -d * γ i)
  have ha : ∀ o, a o ≠ 0 := by
    rintro (_ | i | i)
    · exact neg_ne_zero.mpr hκ
    · exact hγ i
    · exact mul_ne_zero (neg_ne_zero.mpr hd0) (hγ i)
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ Option (Fin r ⊕ Fin r)) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨x, hx, hx0⟩ : ∃ x : Option (Fin r ⊕ Fin r) → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 :=
    isotropic_of_injective e e.injective (H _)
  obtain ⟨w, hw, hw0⟩ := exists_zero_coord h2 ha hx hx0 none
  rw [Fintype.sum_option, Fintype.sum_sum_type] at hw0
  have hw1 := congrArg (algebraMap K L) hw0
  have hw2 : algebraMap K L (w none) ≠ 0 := (map_ne_zero _).2 hw
  simp only [a, Option.elim, Sum.elim_inl, Sum.elim_inr, map_add, map_mul, map_neg, map_pow, map_sum,
    hγ', hκ', hd, map_zero] at hw1
  have hs : ∀ s : K, c (algebraMap K L s) = algebraMap K L s := fun s => (hF _).2 ⟨s, rfl⟩
  refine ⟨fun i => (algebraMap K L (w (some (Sum.inl i))) +
    algebraMap K L (w (some (Sum.inr i))) * θ) / algebraMap K L (w none), ?_⟩
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, map_div₀, map_add, map_mul,
    hs, hθ]
  have : ∀ i, (algebraMap K L (w (some (Sum.inl i))) + algebraMap K L (w (some (Sum.inr i))) * θ) /
      algebraMap K L (w none) * (g i * ((algebraMap K L (w (some (Sum.inl i))) +
        algebraMap K L (w (some (Sum.inr i))) * -θ) / algebraMap K L (w none))) =
      (g i * algebraMap K L (w (some (Sum.inl i))) ^ 2 +
        -(θ * θ) * g i * algebraMap K L (w (some (Sum.inr i))) ^ 2) /
          algebraMap K L (w none) ^ 2 := by
    intro i
    field_simp
    ring
  simp only [this, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [div_eq_iff (pow_ne_zero 2 hw2)]
  linear_combination hw1
end GlobalTheory.HermLocal
