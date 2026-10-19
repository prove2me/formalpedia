-- Prove2me | solution 1 for OAI.Release075.line_two_points
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:21:40.829995+00:00
-- url     : https://prove2.me/submissions/fb41a9d9-2ef6-4532-b50b-62bc1aaf4b63

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L472-L487
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.line_two_points. The node keeps its source
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

/-- Two distinct points determine their direction and every mark on their line. -/
theorem line_two_points (a z z' : V) (d : Projectivization K V) (hzz : z' ≠ z)
    (hz : OnChosenLine a z d) (hz' : OnChosenLine a z' d) :
    ∃ t : K, a = z + t • (z'-z) ∧
      d = Projectivization.mk K (z'-z) (sub_ne_zero.mpr hzz) := by
  obtain ⟨u,hu⟩ := hz
  obtain ⟨v,hv⟩ := hz'
  have hdiff : z'-z = (v-u) • d.rep := by rw [← hu,← hv,sub_smul]; abel
  have hvu : v-u ≠ 0 := by
    intro h; rw [h,zero_smul] at hdiff; exact hzz (sub_eq_zero.mp hdiff)
  refine ⟨-u / (v-u),?_,?_⟩
  · rw [hdiff,smul_smul,div_mul_cancel₀ _ hvu,neg_smul,← hu]
    abel
  · rw [← d.mk_rep,Projectivization.mk_eq_mk_iff']
    refine ⟨(v-u)⁻¹,?_⟩
    rw [hdiff,smul_smul,inv_mul_cancel₀ hvu,one_smul]

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


theorem solution : type_of% @_root_.OAI.Release075.line_two_points := @_root_.OAI.Release075.line_two_points
