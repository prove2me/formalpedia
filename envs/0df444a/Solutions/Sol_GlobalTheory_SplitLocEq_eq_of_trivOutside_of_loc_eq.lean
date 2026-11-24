-- Prove2me | solution 1 for GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:38.744922+00:00
-- url     : https://prove2.me/submissions/1c6140a2-dec0-4b53-b247-954d0a29fdae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfSupportedAtSplit
import Theorems.Thm_GlobalTheory_SplitLocEq_conj_entry
import Theorems.Thm_GlobalTheory_SplitLocEq_proj_entry
import Theorems.Thm_GlobalTheory_tensor_decomp_eq_zero
import Theorems.Thm_GlobalTheory_tensor_exists_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
namespace GlobalTheory.SplitLocEq
open NumberField IsDedekindDomain TensorProduct in
private theorem evalAt_apply' {L : Type} [Field L] [NumberField L] (w)
    (a : _root_.ReciprocityTheory.Aut.AFplus L) : _root_.ReciprocityTheory.Aut.evalAt L w a = a w := rfl
open NumberField IsDedekindDomain TensorProduct in
private theorem eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (d : _root_.ReciprocityTheory.Aut.AL L)
    (hw : ∀ w, w ≠ s.v → _root_.ReciprocityTheory.Aut.compAt L w d = 0) (h₁ : s.proj d = 0)
    (h₂ : s.proj (_root_.ReciprocityTheory.Aut.conjAL L d) = 0) : d = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L :=
    Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  obtain ⟨a, c, rfl⟩ := _root_.GlobalTheory.tensor_exists_decomp b d
  have hw' : ∀ w, w ≠ s.v → a w = 0 ∧ c w = 0 := fun w hne =>
    _root_.GlobalTheory.tensor_decomp_eq_zero b _ _
      (by simpa [_root_.ReciprocityTheory.Aut.compAt, evalAt_apply'] using hw w hne)
  simp only [map_add, _root_.ReciprocityTheory.Aut.SplitPlace.proj, _root_.ReciprocityTheory.Aut.conjAL] at h₁ h₂
  simp [evalAt_apply'] at h₁ h₂
  set σ := IsCMField.complexConj L
  have hΔ : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) ≠ 0 := by
    intro h0
    have h0' : b 0 * σ (b 1) - b 1 * σ (b 0) = 0 :=
      (injective_iff_map_eq_zero s.i.toRingHom).mp (RingHom.injective s.i.toRingHom) _ h0
    have hb1 : b 1 ≠ 0 := b.ne_zero 1
    have hσb1 : σ (b 1) ≠ 0 := by simpa using hb1
    have hfix : σ (b 0 / b 1) = b 0 / b 1 := by
      rw [map_div₀, div_eq_div_iff hσb1 hb1]
      linear_combination -h0'
    obtain ⟨k, hk⟩ : ∃ k : maximalRealSubfield L, (k : L) = b 0 / b 1 :=
      ⟨⟨_, (IsCMField.complexConj_eq_self_iff L _).mp hfix⟩, rfl⟩
    have hsum : ∑ i, (![1, -k] : Fin 2 → maximalRealSubfield L) i • b i = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      have hsm : k • b 1 = (k : L) * b 1 := rfl
      rw [hsm, hk, div_mul_cancel₀ _ hb1]
      ring
    have := Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum 0
    simp at this
  have hA : a s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * a s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (σ (b 1)) * h₁ - s.i (b 1) * h₂
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have hC : c s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * c s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (b 0) * h₂ - s.i (σ (b 0)) * h₁
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have ha : a = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hA
    · exact (hw' w hv).1
  have hc : c = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hC
    · exact (hw' w hv).2
  simp [ha, hc]
end GlobalTheory.SplitLocEq
end

set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
open GlobalTheory GlobalTheory.SplitLocEq
open NumberField IsDedekindDomain TensorProduct
namespace GlobalTheory.SplitLocEq
namespace _root_.GlobalTheory.SplitLocEq
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L]
    [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (x y : _root_.Formalism.AUTREP.GAf L n),
    _root_.ReciprocityTheory.Aut.TrivOutside {s.v} x → _root_.ReciprocityTheory.Aut.TrivOutside {s.v} y → s.loc n x = s.loc n y → x = y := by
  intro L _ _ _ n s x y hx hy hxy
  have triv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z → ∀ w, w ≠ s.v → ∀ i j,
      _root_.ReciprocityTheory.Aut.compAt L w ((z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro z hz w hw i j
    have := hz w (by simpa using hw)
    exact congrFun (congrFun this i) j
  have trivInv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z → _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z⁻¹ := by
    intro z hz w hw
    show ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)).map (_root_.ReciprocityTheory.Aut.compAt L w) = 1
    have hm : (z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) *
        ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1 := by simp
    have h2 := congrArg (Matrix.map · (_root_.ReciprocityTheory.Aut.compAt L w)) hm
    simp only [Matrix.map_mul] at h2
    rw [hz w hw, one_mul] at h2
    rw [h2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hinv : s.loc n x⁻¹ = s.loc n y⁻¹ := by simp [map_inv, hxy]
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero s
  · intro w hw
    rw [map_sub, triv x hx w hw, triv y hy w hw, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hxy, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.conj_entry, _root_.GlobalTheory.SplitLocEq.conj_entry,
      map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hinv, sub_self]
end _root_.GlobalTheory.SplitLocEq
end GlobalTheory.SplitLocEq
