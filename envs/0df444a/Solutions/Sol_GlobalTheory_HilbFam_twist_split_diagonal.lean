-- Prove2me | solution 1 for GlobalTheory.HilbFam.twist_split_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:24:47.276583+00:00
-- url     : https://prove2.me/submissions/ac1d7199-9d4d-4af5-9b09-1f8a9a90f4b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertSplitLatticeTwistDiagonalCoprime
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_T_mem_hilbertLatticeTwist_iff_lift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  intro F _ _ _ N 𝔞 𝔟 x a hcop hlev
  have hstd : ∀ w : Fin 2 → F, w ∈ stdLat F ↔ ∀ i, w i ∈ (1 : Submodule (𝓞 F) F) := by
    intro w; simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  have hsp : ∀ (z : F) (w : Fin 2 → F), w ∈ split 𝔞 𝔟 z ↔
      w 0 ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) ∧
      w 1 - w 0 * z ∈ (latM 𝔞 : Submodule (𝓞 F) F) := fun _ _ ↦ Iff.rfl
  have hA : (Matrix.diagonal ![1, (a : ZMod N)]) =
      (Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → ZMod N) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hv0 : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → F)) = ![y 0, a * y 1] := by
    intro y
    ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  have hN : ∀ w ∈ stdLat F, (N : F) • w ∈ split 𝔞 𝔟 x := by
    intro w hw
    have h := hlev.1 w hw
    rw [Nat.cast_smul_eq_nsmul] at h ⊢
    exact h
  have hz : ∀ (n : ℤ) (S : Submodule (𝓞 F) F) (m : F), m ∈ S → (n : F) * m ∈ S := by
    intro n S m hm
    rw [← zsmul_eq_mul]
    exact zsmul_mem hm n
  ext v
  rw [hA, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ _ v hlev.2]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    rw [hv0]
    have hw' := (hstd w).1 hw
    have h0 := (hsp _ _).1 (hN ![w 0, 0] ((hstd _).2 (by
      intro i; fin_cases i
      · exact hw' 0
      · exact Submodule.zero_mem _)))
    have h1 := (hsp _ _).1 (hN ![0, w 1] ((hstd _).2 (by
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hw' 1)))
    have hy' := (hsp _ _).1 hy
    rw [hsp]
    refine ⟨?_, ?_⟩
    · have := Submodule.add_mem _ hy'.1 h0.1
      convert this using 1
      simp
    · have := Submodule.add_mem _ (Submodule.add_mem _ (hz a _ _ hy'.2) h1.2) (hz a _ _ h0.2)
      convert this using 1
      simp
      ring
  · intro hv
    have hv' := (hsp _ _).1 hv
    obtain ⟨u, t, hut⟩ := hcop
    have hut' : (u : F) * a + t * N = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → F) hut
    have hm : ![0, v 1 - v 0 * (a * x)] ∈ split 𝔞 𝔟 x := by
      rw [hsp]
      refine ⟨Submodule.zero_mem _, ?_⟩
      convert hv'.2 using 1
      simp
    have hm' := (hstd _).1 (hlev.2 hm) 1
    refine ⟨![v 0, v 0 * x + u * (v 1 - v 0 * (a * x))], ?_, ![0, t * (v 1 - v 0 * (a * x))], ?_, ?_⟩
    · rw [hsp]
      refine ⟨hv'.1, ?_⟩
      convert hz u _ _ hv'.2 using 1
      simp
    · rw [hstd]
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hz t _ _ hm'
    · rw [hv0]
      ext j; fin_cases j
      · simp
      · simp
        linear_combination (-(v 1 - v 0 * (a * x))) * hut'
end GlobalTheory.HilbFam
