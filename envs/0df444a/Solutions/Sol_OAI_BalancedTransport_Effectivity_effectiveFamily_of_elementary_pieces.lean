-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.effectiveFamily_of_elementary_pieces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:58:58.694979+00:00
-- url     : https://prove2.me/submissions/e6e198eb-38a8-4e57-bcc1-9ef47aab2f00

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveGluing.lean:L223-L287
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.effectiveFamily_of_elementary_pieces. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveGluing
import Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_rat_le
import Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_jet_evaluators
import Theorems.Thm_OAI_BalancedTransport_Geometry_fullMixedD_eq_mixedD

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RationalAlgorithms ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_rat_sub : Computable₂ ((· - ·) : ℚ → ℚ → ℚ) := by
  exact (computable_rat_add.comp Computable.fst (computable_rat_neg.comp Computable.snd)).of_eq
    (fun _ => (sub_eq_add_neg _ _).symm)

lemma computable_rat_natCast : Computable (fun n : ℕ => (n : ℚ)) := by
  exact (computable_rat_of_parts primrec_int_ofNat.to_comp (Computable.const 1)
    (fun _ => by decide)).of_eq (fun n => by norm_cast; simp)

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FieldBounds ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

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

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveLog ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

lemma computable_rat_lt : Computable₂ (fun a b : ℚ => decide (a < b)) := by
  exact (Computable.cond (computable_rat_le.comp Computable.snd Computable.fst)
    (Computable.const false) (Computable.const true)).of_eq
      (fun p => by
        by_cases h : p.2 ≤ p.1
        · simp [h, not_lt.mpr h]
        · simp [h, lt_of_not_ge h])

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TemporalJets ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Filter Set
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma timeGerm_fullTimeD {v w : Field F} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    fullTimeD v =ᶠ[𝓝 t] fullTimeD w := by
  filter_upwards [h.eventually_nhds] with s hs
  funext x
  have he : (fun r => v r x) =ᶠ[𝓝 s] (fun r => w r x) := hs.mono (fun _ he => congrFun he x)
  exact he.deriv_eq

lemma timeGerm_spaceD {v w : Field F} {t : ℝ} (h : v =ᶠ[𝓝 t] w) (i : Fin 3) :
    spaceD i v =ᶠ[𝓝 t] spaceD i w := by
  filter_upwards [h] with s hs
  funext x
  change fderiv ℝ (v s) x _ = fderiv ℝ (w s) x _
  rw [hs]

lemma timeGerm_fullMixedD {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) (a : MultiIndex) :
    fullMixedD a v =ᶠ[𝓝 t] fullMixedD a w := by
  induction a with
  | nil => exact h
  | cons i a ih => cases i with
    | none => exact timeGerm_fullTimeD ih
    | some i => exact timeGerm_spaceD ih i

lemma fullTimeD_translate (v : Field F) (b : ℝ) :
    fullTimeD (fun t => v (t-b)) = fun t => fullTimeD v (t-b) := by
  funext t x
  exact deriv_comp_sub_const (fun s => v s x) b t

lemma fullMixedD_translate (v : Velocity) (a : MultiIndex) (b : ℝ) :
    fullMixedD a (fun t => v (t-b)) = fun t => fullMixedD a v (t-b) := by
  induction a with
  | nil => rfl
  | cons i a ih => cases i with
    | none => simp only [fullMixedD, ih, fullTimeD_translate]
    | some i => simp only [fullMixedD, ih]; rfl

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveGluing ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

lemma computable_rationalNatFloor : Computable rationalNatFloor :=
  Primrec.nat_div.to_comp.comp (primrec_int_toNat.to_comp.comp computable_rat_num)
    computable_rat_den

lemma rationalNatFloor_eq {q : ℚ} (hq : 0 ≤ q) : rationalNatFloor q = ⌊q⌋₊ := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have he : ((q.num.toNat : ℕ) : ℚ) / (q.den : ℚ) = q := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, Rat.num_div_den]
  conv_rhs => rw [← he, Rat.natFloor_natCast_div_natCast]
  rfl

lemma rationalNatFloor_cast {q : ℚ} (hq : 0 ≤ q) :
    (rationalNatFloor q : ℝ) = (⌊(q : ℝ)⌋ : ℤ) := by
  rw [Rat.floor_cast, rationalNatFloor_eq hq, ← Int.natCast_floor_eq_floor hq]
  simp

lemma computable_rationalPhase : Computable rationalPhase := by
  apply computable_ite (computable_rat_lt.comp Computable.id (Computable.const 1)) Computable.id
  exact computable_rat_sub.comp Computable.id
    (computable_rat_natCast.comp computable_rationalNatFloor)

lemma rationalPhase_cast (q : ℚ) (hq : 0 ≤ q) :
    (rationalPhase q : ℝ) = if (q : ℝ) < 1 then (q : ℝ) else (q : ℝ) - (⌊(q : ℝ)⌋ : ℤ) := by
  by_cases h : q < 1
  · have hr : (q : ℝ) < 1 := by exact_mod_cast h
    simp [rationalPhase,h,hr]
  · have hr : ¬ (q : ℝ) < 1 := by exact_mod_cast h
    simp [rationalPhase,h,hr,rationalNatFloor_cast hq]

lemma rationalPhase_bound (q : ℚ) (hq : 0 ≤ q) : |(rationalPhase q : ℝ)| ≤ 1 := by
  rw [rationalPhase_cast q hq]
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast hq)]
    exact h.le
  · have hlo := Int.floor_le (q : ℝ)
    have hhi := Int.lt_floor_add_one (q : ℝ)
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma ElementaryPieces.jet {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F)
    (M : FiniteMachine) (w : Input M) (a : MultiIndex) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    fullMixedD a (F M w) t x =
      if t < 1 then fullMixedD a (L (fun i => (κ (inputCode M w) i : ℝ))) t x
      else fullMixedD a (V (fun i => (κ (inputCode M w) i : ℝ))) (t - (⌊t⌋ : ℤ)) x := by
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact congrFun (timeGerm_fullMixedD hh a |>.self_of_nhds) x
  · simpa only [fullMixedD_translate] using
      (congrFun (timeGerm_fullMixedD hh a |>.self_of_nhds) x)

theorem effectiveFamily_of_elementary_pieces {d : ℕ}
    {L V : (Fin d → ℝ) → Velocity} (hL : ElementaryField L) (hV : ElementaryField V)
    (hsL : ∀p, JointSmooth (L p)) (hsV : ∀p, JointSmooth (V p))
    {κ : ℕ → Fin d → ℚ} (hκ : Computable κ) (C R : ℕ)
    (hC : ∀n i, |(κ n i : ℝ)| ≤ C) {F : Family Velocity}
    (hF : ∀M w, JointSmooth (F M w))
    (hS : ∀M w, SpatiallySupported (Metric.closedBall (0 : Space) R) (F M w))
    (hp : ElementaryPieces L V κ F) : EffectiveFamily F := by
  obtain ⟨EL,bL,hEL,hbL,heL,hmL⟩ := elementary_jet_evaluators hL hsL hκ C hC
  obtain ⟨EV,bV,hEV,hbV,heV,hmV⟩ := elementary_jet_evaluators hV hsV hκ C hC
  let phaseInput : (ℕ × MultiIndex × RationalPoint × ℕ) →
      (ℕ × MultiIndex × RationalPoint × ℕ) :=
    fun z => (z.1,z.2.1,(rationalPhase z.2.2.1.1,z.2.2.1.2),z.2.2.2)
  have hc : Computable phaseInput := by
    dsimp only [phaseInput]
    exact Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (((computable_rationalPhase.comp (Computable.fst.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))).pair
        (Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))).pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  let E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ :=
    fun z => if z.2.2.1.1 < 1 then EL (phaseInput z) else EV (phaseInput z)
  have hE : Computable E :=
    computable_ite (computable_rat_lt.comp (Computable.fst.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd))) (Computable.const 1))
      (hEL.comp hc) (hEV.comp hc)
  let b : ℕ × MultiIndex → ℕ := fun z => bL (z.2,R) + bV (z.2,R)
  have hb : Computable b := Primrec.nat_add.to_comp.comp
    (hbL.comp (Computable.snd.pair (Computable.const R)))
    (hbV.comp (Computable.snd.pair (Computable.const R)))
  refine ⟨E,b,(fun _ => R),hE,hb,Computable.const R,?_,?_,?_⟩
  · intro M w a z n hz i
    have ht : 0 ≤ (z.1 : ℝ) := by exact_mod_cast hz
    rw [← fullMixedD_eq_mixedD (hF M w) a _ ht _, hp.jet M w a _ ht _]
    dsimp only [E,phaseInput]
    by_cases hz' : z.1 < 1
    · have hr : (z.1 : ℝ) < 1 := by exact_mod_cast hz'
      simp only [ite_eq_left hz',ite_eq_left hr]
      have he := heL (inputCode M w) a (rationalPhase z.1,z.2) n
        (rationalPhase_bound _ hz) i
      simpa only [rationalPhase,ite_eq_left hz'] using he
    · have hr : ¬(z.1 : ℝ) < 1 := by exact_mod_cast hz'
      simp only [ite_eq_right hz',ite_eq_right hr]
      have he := heV (inputCode M w) a (rationalPhase z.1,z.2) n
        (rationalPhase_bound _ hz) i
      simpa only [rationalPhase_cast _ hz,ite_eq_right hr] using he
  · intro M w a t ht x
    rw [← fullMixedD_eq_mixedD (hF M w) a _ ht _]
    by_cases hx : ‖x‖ ≤ (R : ℝ)
    · rw [hp.jet M w a t ht x]
      split_ifs with hlt
      · have he := hmL (inputCode M w) a t x R
          (by rw [abs_of_nonneg ht]; exact hlt.le) hx
        exact he.trans (by dsimp [b]; push_cast; exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      · have hlo := Int.floor_le t
        have hhi := Int.lt_floor_add_one t
        have he := hmV (inputCode M w) a (t-(⌊t⌋ : ℤ)) x R
          (by rw [abs_of_nonneg (by linarith)]; linarith) hx
        exact he.trans (by dsimp [b]; push_cast; exact le_add_of_nonneg_left (Nat.cast_nonneg _))
    · have he := (hS M w).fullMixedD Metric.isClosed_closedBall a t x
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
      rw [he, norm_zero]
      exact Nat.cast_nonneg _
  · intro M w t _ x hx
    exact hS M w t x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.effectiveFamily_of_elementary_pieces := @_root_.OAI.BalancedTransport.Effectivity.effectiveFamily_of_elementary_pieces
