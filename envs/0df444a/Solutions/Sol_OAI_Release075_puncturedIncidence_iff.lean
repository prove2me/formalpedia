-- Prove2me | solution 1 for OAI.Release075.puncturedIncidence_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:07:19.850294+00:00
-- url     : https://prove2.me/submissions/71690311-0ad1-4a95-91cb-235081afb6cd

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L158-L174
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.puncturedIncidence_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- At a point different from the mark, exactly one direction gives incidence. -/
theorem puncturedIncidence_iff (a z : V) (hza : z ≠ a) (d : Projectivization K V) :
    PuncturedIncidence a z d ↔ d = Projectivization.mk K (z-a) (sub_ne_zero.mpr hza) := by
  have hd := d.mk_rep
  rw [PuncturedIncidence, and_iff_right hza]
  constructor
  · rintro ⟨t,ht⟩
    rw [← hd, Projectivization.mk_eq_mk_iff']
    have ht' : t • d.rep = z-a := by rw [← ht]; abel
    have ht0 : t ≠ 0 := by intro h; simp [h] at ht; exact hza ht.symm
    refine ⟨t⁻¹, ?_⟩
    rw [← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]
  · intro h
    have hh := (Projectivization.mk_eq_mk_iff' K (z-a) d.rep
      (sub_ne_zero.mpr hza) d.rep_nonzero).mp (h.symm.trans hd.symm)
    obtain ⟨t,ht⟩ := hh
    exact ⟨t, by rw [ht]; abel⟩

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.Release075.puncturedIncidence_iff := @_root_.OAI.Release075.puncturedIncidence_iff
