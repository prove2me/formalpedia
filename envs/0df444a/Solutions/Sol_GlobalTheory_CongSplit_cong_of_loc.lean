-- Prove2me | solution 1 for GlobalTheory.CongSplit.cong_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:17.353915+00:00
-- url     : https://prove2.me/submissions/57500863-4b9b-48f8-b29c-56cecdd6f1b1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CongOfLoc
import Theorems.Thm_GlobalTheory_CongSplit_conj_entry
import Theorems.Thm_GlobalTheory_SplitSep_exists_sep
import Theorems.Thm_GlobalTheory_mem_ALint_of_supported_at_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
open GlobalTheory GlobalTheory.CongSplit
namespace GlobalTheory.CongSplit
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (N : ℕ), 0 < N →
    ∀ x : GAf L n, TrivOutside {s.v} x →
    (∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    (∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    NG.Cong L n N x := by
  intro L _ _ _ n s N hN x hx h1 h2
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hNL : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1 := ⟨algebraMap L (AL L) (N : L)⁻¹, by
    rw [← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hNL, map_one]⟩
  have key : ∀ (f : AL L →+* s.v.adicCompletion (maximalRealSubfield L)) (z : AL L),
      Valued.v (f z) ≤ Valued.v ((N : s.v.adicCompletion (maximalRealSubfield L))) → Valued.v (f (u * z)) ≤ 1 := by
    intro f z hz
    have h := congrArg (fun t => Valued.v (f t)) hu
    simp only [map_mul, map_natCast, map_one] at h
    rw [map_mul, map_mul, ← h, mul_comm]
    exact mul_le_mul_left hz _
  suffices H : ∀ i j : Fin n, ∃ y ∈ ALint L, (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y by
    refine ⟨fun i j => ?_, H⟩
    obtain ⟨y, hy, hxy⟩ := H i j
    rw [sub_eq_iff_eq_add.1 hxy]
    refine add_mem (mul_mem (natCast_mem _ N) hy) ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem]
  intro i j
  refine ⟨u * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j), ?_, ?_⟩
  · apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_mul, map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · apply key
      have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl
      have e2 : s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [map_sub, e1, e2]
      exact h1 i j
    · apply key (s.proj.comp (conjAL L))
      have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := rfl
      have e2 : (s.proj.comp (conjAL L)) ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := by
        by_cases hij : i = j
        · simp [Matrix.one_apply, hij]
        · simp [Matrix.one_apply, hij, Ne.symm hij]
      rw [map_sub, e2, RingHom.comp_apply, conj_entry, e1]
      exact h2 j i
  · rw [← mul_assoc, hu, one_mul]
end GlobalTheory.CongSplit
