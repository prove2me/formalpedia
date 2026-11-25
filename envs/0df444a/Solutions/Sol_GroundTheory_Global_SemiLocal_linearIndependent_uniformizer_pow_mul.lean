-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.linearIndependent_uniformizer_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:13.175577+00:00
-- url     : https://prove2.me/submissions/07bc128b-59c0-49dc-8e90-d8c10cf50b80

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_field
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_sum_eq
import Theorems.Thm_GroundTheory_Global_SemiLocal_eq_of_exp_mul_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]
omit [Fintype ι]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution [Finite ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (π : L) (hπ : w.valuation L π = exp (-1 : ℤ)) :
    LinearIndependent (v.adicCompletion K)
      (fun p : Fin (w.asIdeal.ramificationIdx (𝓞 K)) × ι ↦
        algebraMap L (w.adicCompletion L) π ^ (p.1 : ℕ) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω p.2)) := by
  classical
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact linearIndependent_empty_type
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  set P := algebraMap L (w.adicCompletion L) π with hP
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set s : Fin e → w.adicCompletion L := fun i ↦
    ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (g (i, j)) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j) with hs_def
  have hsum : ∑ i : Fin e, P ^ (i : ℕ) * s i = 0 := by
    rw [← hg, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hs_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def]
    ring
  have hvP : ∀ n : ℕ, Valued.v (P ^ n) = exp (-(n : ℤ)) := by
    intro n
    rw [map_pow, hP, valued_algebraMap_field, hπ, ← exp_nsmul]
    simp
  choose J hJ using fun i : Fin e ↦ Finite.exists_max (fun j ↦ Valued.v (g (i, j)))
  set M : Fin e → ℤᵐ⁰ := fun i ↦ Valued.v (g (i, J i)) with hM_def
  have hterm : ∀ i : Fin e, Valued.v (P ^ (i : ℕ) * s i) = exp (-((i : ℕ) : ℤ)) * M i ^ e := by
    intro i
    rw [map_mul, hvP, hs_def, valued_sum_eq v w ω hω _ (J i) (hJ i)]
  have hM : ∀ i, M i = 0 := by
    by_contra hne
    obtain ⟨i1, hi1⟩ := not_forall.1 hne
    have : Nonempty (Fin e) := ⟨i1⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i : Fin e ↦ Valued.v (P ^ (i : ℕ) * s i))
    have hnz : ∀ i : Fin e, Valued.v (P ^ (i : ℕ) * s i) ≠ 0 → M i ≠ 0 := by
      intro i hi hMi
      rw [hterm, hMi, zero_pow he0, mul_zero] at hi
      exact hi rfl
    have htop : Valued.v (P ^ (i0 : ℕ) * s i0) ≠ 0 := by
      intro h
      have := hi0 i1
      rw [h, hterm] at this
      have h' : exp (-((i1 : ℕ) : ℤ)) * M i1 ^ e = 0 := le_antisymm this zero_le
      rw [mul_eq_zero] at h'
      rcases h' with h' | h'
      · exact exp_ne_zero h'
      · exact hi1 (pow_eq_zero_iff he0 |>.1 h')
    have hlt : ∀ i ∈ Finset.univ \ {i0},
        Valued.v (P ^ (i : ℕ) * s i) < Valued.v (P ^ (i0 : ℕ) * s i0) := by
      intro i hi
      have hne : i ≠ i0 := by simpa using hi
      refine lt_of_le_of_ne (hi0 i) fun heq ↦ hne (Fin.ext ?_)
      have hi_nz : Valued.v (P ^ (i : ℕ) * s i) ≠ 0 := heq ▸ htop
      rw [hterm, hterm] at heq
      exact eq_of_exp_mul_pow_eq i.2 i0.2 (hnz i hi_nz) (hnz i0 htop) heq
    have := Valuation.map_sum_eq_of_lt _ (Finset.mem_univ i0) hlt
    rw [hsum, map_zero] at this
    exact htop this.symm
  rintro ⟨i, j⟩
  have := hJ i j
  rw [show Valued.v (g (i, J i)) = M i from rfl, hM i] at this
  exact (Valuation.zero_iff _).1 (le_antisymm this zero_le)
end GroundTheory.Global.SemiLocal
