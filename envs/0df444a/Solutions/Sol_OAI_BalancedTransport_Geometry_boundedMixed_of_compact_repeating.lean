-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.boundedMixed_of_compact_repeating
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:24:07.327475+00:00
-- url     : https://prove2.me/submissions/272f1eb8-be16-4088-b397-6d24c7653d6b

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FieldBounds.lean:L131-L147
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.boundedMixed_of_compact_repeating. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Theorems.Thm_OAI_BalancedTransport_Geometry_RepeatsAfter_fullTimeD
import Theorems.Thm_OAI_BalancedTransport_Geometry_fullMixedD_eq_mixedD

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TimeRegularity ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem JointSmooth.spaceD {f : Field F} (hf : JointSmooth f) (i : Fin 3) :
    JointSmooth (spaceD i f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × Space => f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv_apply contDiff_snd contDiff_const (by simp)

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FieldBounds ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma JointSmooth.fullMixedD {v : Field F} (hv : JointSmooth v) (a : MultiIndex) :
    JointSmooth (fullMixedD a v) := by
  induction a with
  | nil => exact hv
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD i

lemma SpatiallySupported.spaceD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) (hK : IsClosed K) (i : Fin 3) :
    SpatiallySupported K (spaceD i v) := by
  intro t x hx
  have he : v t =ᶠ[𝓝 x] 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact h t y hy
  change fderiv ℝ (v t) x (Pi.single i 1) = 0
  rw [he.fderiv_eq]
  simp

lemma SpatiallySupported.fullMixedD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) (hK : IsClosed K) (a : MultiIndex) :
    SpatiallySupported K (fullMixedD a v) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD hK i

lemma RepeatsAfter.spaceD {T : ℝ} {v : Field F} (h : RepeatsAfter T v) (i : Fin 3) :
    RepeatsAfter T (spaceD i v) := by
  intro t ht
  funext x
  change fderiv ℝ (v (t + 1)) x (Pi.single i 1) = fderiv ℝ (v t) x (Pi.single i 1)
  rw [h t ht]

lemma RepeatsAfter.fullMixedD {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    (hv : JointSmooth v) (a : MultiIndex) : RepeatsAfter T (fullMixedD a v) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD (hv.fullMixedD a)
      | some i => exact ha.spaceD i

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
lemma RepeatsAfter.add_nat {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    {t : ℝ} (ht : T ≤ t) (n : ℕ) : v (t + n) = v t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, h _ (by linarith [Nat.cast_nonneg (α := ℝ) n]), ih]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
lemma RepeatsAfter.reduce {v : Field F} (h : RepeatsAfter 1 v) {t : ℝ} (ht : 0 ≤ t) :
    ∃ s ∈ Icc (0 : ℝ) 2, v t = v s := by
  by_cases ht' : t ≤ 2
  · exact ⟨t, ⟨ht, ht'⟩, rfl⟩
  · have htn : 0 ≤ t - 1 := by linarith
    let n := ⌊t - 1⌋₊
    have hle : (n : ℝ) ≤ t - 1 := Nat.floor_le htn
    have hlt : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - 1)
    refine ⟨t - n, ⟨by linarith, by linarith⟩, ?_⟩
    have he := h.add_nat (t := t - n) (by linarith) n
    simpa using he

theorem boundedMixed_of_compact_repeating {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v)
    (hp : RepeatsAfter 1 v) : BoundedMixed v := by
  intro a
  have ha := hv.fullMixedD a
  have hsa := hs.fullMixedD hK.isClosed a
  have hpa := hp.fullMixedD hv a
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    ha.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  rw [← fullMixedD_eq_mixedD hv a t ht x]
  obtain ⟨s, hs, he⟩ := hpa.reduce ht
  rw [congrFun he x]
  by_cases hx : x ∈ K
  · exact (hC (s, x) ⟨hs,hx⟩).trans (le_max_left _ _)
  · rw [hsa s x hx, norm_zero]
    exact le_max_right _ _

end BalancedTransport.Geometry
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.boundedMixed_of_compact_repeating := @_root_.OAI.BalancedTransport.Geometry.boundedMixed_of_compact_repeating
