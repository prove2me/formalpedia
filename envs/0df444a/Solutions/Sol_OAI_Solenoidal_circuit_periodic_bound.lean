-- Prove2me | solution 1 for OAI.Solenoidal.circuit_periodic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:44:46.136247+00:00
-- url     : https://prove2.me/submissions/6e35fd85-3e60-4082-a1c0-9e07f2629de3

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/CircuitPrograms.lean:L211-L226
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.circuit_periodic_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Circuits
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_CircuitPrograms
import Theorems.Thm_OAI_Solenoidal_flatJet_bound
import Theorems.Thm_OAI_Solenoidal_mixedDerivative_eqOn_cell
import Theorems.Thm_OAI_Solenoidal_transitionReciprocal_bound

-- ---- from OAI.MathematicalPhysics.SheetFlows.Differential ----
namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_contDiff {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (directional g v) :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

theorem directional_translation {g : E → F} (hg : Differentiable ℝ g)
    {c : E} (hc : ∀ x, g (x + c) = g x) (v x : E) :
    directional g v (x + c) = directional g v x := by
  have hd := (hg (x + c)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const c)
  have he : (fun y => g (y + c)) = g := funext hc
  have hd' : HasFDerivAt g (fderiv ℝ g (x + c)) x := by simpa only [Function.comp_def, id_eq, he, ContinuousLinearMap.comp_id] using hd
  exact (congrArg (fun L : E →L[ℝ] F => L v) hd'.fderiv).symm

end DirectionalCalculus

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ScheduledForce ----
namespace OAI

/-! SheetFlows scheduled force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem mixedDerivative_contDiff {u : Field} (hu : Smooth u) (α : List (Fin 4)) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedDerivative u α) := by
  induction α with
  | nil => exact hu
  | cons j α ih => exact directional_contDiff ih (spacetimeBasis j)

theorem mixedDerivative_translation {u : Field} (hu : Smooth u)
    (c : SpaceTime) (hc : ∀ z : SpaceTime, u (z + c).1 (z + c).2 = u z.1 z.2)
    (α : List (Fin 4)) (z : SpaceTime) :
    mixedDerivative u α (z + c) = mixedDerivative u α z := by
  induction α generalizing z with
  | nil => exact hc z
  | cons j α ih =>
    exact directional_translation ((mixedDerivative_contDiff hu α).differentiable (by simp))
      ih (spacetimeBasis j) z

theorem mixedDerivative_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (α : List (Fin 4)) :
    SpatiallyPeriodic (fun t x => mixedDerivative u α (t, x)) := by
  intro t x k
  have h := mixedDerivative_translation hu (0, deck k)
    (fun z => by simpa using hp z.1 z.2 k) α (t, x)
  simpa using h

theorem mixedDerivative_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (α : List (Fin 4)) :
    OnePeriodic (fun t x => mixedDerivative u α (t, x)) := by
  intro t x
  have h := mixedDerivative_translation hu (1, 0)
    (fun z => by simpa using hp z.1 z.2) α (t, x)
  simpa using h

theorem wrapSpace_mem (x : Space) : wrapSpace x ∈ Set.Icc 0 (fun _ => 10) := by
  constructor <;> intro j
  · exact mul_nonneg (by norm_num) (Int.fract_nonneg _)
  · have := Int.fract_lt_one (x j / 10)
    change 10 * Int.fract (x j / 10) ≤ 10
    linarith

theorem wrapSpace_add_deck (x : Space) :
    wrapSpace x + deck (fun j => ⌊x j / 10⌋) = x := by
  ext j
  simp only [Pi.add_apply, wrapSpace, deck, Int.fract]
  ring

theorem periodic_field_reduction {u : Field} (hspace : SpatiallyPeriodic u)
    (htime : OnePeriodic u) (t : ℝ) (x : Space) :
    u t x = u (Int.fract t) (wrapSpace x) := by
  calc
    u t x = u t (wrapSpace x) := by
      conv_lhs => rw [← wrapSpace_add_deck x]
      exact hspace t (wrapSpace x) _
    _ = u (Int.fract t) (wrapSpace x) := by
      have hp : Function.Periodic (fun s => u s (wrapSpace x)) 1 :=
        fun s => htime s (wrapSpace x)
      have h := hp.int_mul ⌊t⌋ (Int.fract t)
      simpa only [mul_one, Int.fract_add_floor] using h

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.JetCalculus ----
namespace OAI

/-! SheetFlows jet calculus. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial
namespace Solenoidal

theorem flatJet_smooth (p : ℚ[X]) : ContDiff ℝ (⊤ : ℕ∞) (flatJet p) :=
  expNegInvGlue.contDiff_polynomial_eval_inv_mul _

theorem transitionReciprocal_smooth : ContDiff ℝ (⊤ : ℕ∞) transitionReciprocal := by
  exact (expNegInvGlue.contDiff.add
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))).inv
      (fun x => (Real.smoothTransition.pos_denom x).ne')

namespace JetExpr

end JetExpr

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Circuits ----
namespace OAI

/-! SheetFlows circuits. -/

section
open Set Filter Encodable Denumerable
open scoped BigOperators Topology Polynomial
namespace Solenoidal

theorem flatJet_sub (p q : ℚ[X]) : flatJet (p-q) = flatJet p - flatJet q := by
  funext x
  simp [flatJet,sub_mul]

theorem flatJet_C_mul (a : ℚ) (p : ℚ[X]) :
    flatJet (Polynomial.C a*p) = fun x => (a:ℝ)*flatJet p x := by
  funext x
  simp [flatJet,mul_assoc]

theorem flatMono_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (flatMono n) (flatMono (n+2) x - (n:ℝ)*flatMono (n+1) x) x := by
  have hp : flatNext (Polynomial.X^n) =
      Polynomial.X^(n+2) - Polynomial.C (n:ℚ)*Polynomial.X^(n+1) := by
    cases n with
    | zero => simp [flatNext]
    | succ n =>
      rw [flatNext, Polynomial.derivative_X_pow]
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  have h := flatJet_hasDerivAt (Polynomial.X^n) x
  rw [hp,flatJet_sub,flatJet_C_mul] at h
  simpa [flatMono] using h

theorem flatMono_bound (n : ℕ) (x : ℝ) : |flatMono n x| ≤ (n.factorial:ℝ) := by
  have h : flatBound (Polynomial.X^n) = (n.factorial:ℚ) := by simp [flatBound, Polynomial.support_X_pow]
  simpa only [flatMono, h, Rat.cast_natCast] using flatJet_bound (Polynomial.X^n) x

namespace Atom

theorem profile_smooth (k : ℕ) : ContDiff ℝ (⊤:ℕ∞) (profile k) := by
  unfold profile
  split
  · exact contDiff_id
  · split
    · exact transitionReciprocal_smooth
    · exact flatJet_smooth _

theorem smooth (a : Atom) : ContDiff ℝ (⊤:ℕ∞) a.eval :=
  (profile_smooth _).comp
    ((contDiff_const.mul (coordinateLinear a.1).contDiff).add contDiff_const)

theorem bound_nonneg (a : Atom) (R : ℚ) : 0 ≤ a.bound R := by
  unfold bound
  split
  · positivity
  · split <;> positivity

theorem bound_correct (a : Atom) (R : ℚ) (z : SpaceTime)
    (hz : ∀ j, |coordinateLinear j z| ≤ |(R:ℝ)|) :
    |a.eval z| ≤ (a.bound R:ℝ) := by
  unfold eval profile bound
  split
  · simp only [id_eq,Rat.cast_add,Rat.cast_mul,Rat.cast_abs]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hz a.1) (abs_nonneg _)) le_rfl
  · split
    · exact transitionReciprocal_bound _
    · simpa using flatMono_bound _ _

end Atom

namespace Circuit

open Nat.Partrec

theorem smooth (e : Circuit) : ContDiff ℝ (⊤:ℕ∞) (eval e) := by
  induction e with
  | zero | succ | left | right => exact contDiff_const
  | pair a b ha hb => exact ha.add hb
  | comp a b ha hb => exact ha.mul hb
  | prec a b ha hb => exact Atom.smooth _
  | rfind' a ha => exact contDiff_const

theorem bound_nonneg (e : Circuit) (R : ℚ) : 0 ≤ bound e R := by
  induction e with
  | zero | succ | left | right => exact le_rfl
  | pair a b ha hb => exact add_nonneg ha hb
  | comp a b ha hb => exact mul_nonneg ha hb
  | prec a b ha hb => exact Atom.bound_nonneg _ _
  | rfind' a ha => exact abs_nonneg _

theorem bound_correct (e : Circuit) (R : ℚ) (z : SpaceTime)
    (hz : ∀ j, |coordinateLinear j z| ≤ |(R:ℝ)|) :
    |(eval e) z| ≤ (bound e R:ℝ) := by
  induction e with
  | zero | succ | left | right => simp [eval,bound]
  | pair a b ha hb =>
    simpa [eval,bound] using (abs_add_le (eval a z) (eval b z)).trans (add_le_add ha hb)
  | comp a b ha hb =>
    have h := mul_le_mul ha hb (abs_nonneg _) (by exact_mod_cast bound_nonneg a R)
    simpa [eval,bound,abs_mul] using h
  | prec a b ha hb => exact Atom.bound_correct _ _ _ hz
  | rfind' a ha => simp [eval,bound]

end Circuit
end Solenoidal
end

open Set Filter Encodable Denumerable
open scoped BigOperators Topology Polynomial
namespace Solenoidal
namespace Atom

theorem profile_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (profile k) (profileDerivative k x) x := by
  unfold profile profileDerivative
  split
  · exact hasDerivAt_id x
  · split
    · exact transitionReciprocal_hasDerivAt x
    · exact flatMono_deriv _ x

end Atom
namespace Circuit
open Nat.Partrec

theorem atomDiff_eval (j : Fin 4) (a : Atom) (z : SpaceTime) :
    eval (atomDiff j a) z =
      (a.2.1:ℝ) * Atom.profileDerivative a.2.2.2
        ((a.2.1:ℝ)*coordinateLinear a.1 z+a.2.2.1) * (if a.1=j then 1 else 0) := by
  unfold atomDiff
  split
  · simp only [eval_mul,eval_const,mul_one]
    congr 1
    unfold Atom.profileDerivative
    split
    · simp
    · split
      · rename_i h h0 h1
        have he : (-(a.2.1:ℝ))*coordinateLinear a.1 z+(1-(a.2.2.1:ℝ)) =
            1-((a.2.1:ℝ)*coordinateLinear a.1 z+a.2.2.1) := by ring
        simp only [eval_mul,eval_const,eval_sub,eval_atom]
        simp [Atom.eval,Atom.profile,Atom.withKind,Atom.reflect,h1]
        left
        congr 1
        ring
      · rename_i h h0 h1
        simp only [eval_sub,eval_const,eval_mul,eval_atom]
        simp [Atom.eval,Atom.withKind,Atom.profile,
          show a.2.2.2-2+4≠1 by omega,
          show a.2.2.2-2+3≠1 by omega]
  · simp_all

theorem diff_correct (e : Circuit) (j : Fin 4) (z : SpaceTime) :
    eval (diff j e) z = fderiv ℝ (eval e) z (spacetimeBasis j) := by
  induction e with
  | zero | succ | left | right => simp [diff,eval]
  | pair a b ha hb =>
      simp only [diff,eval_add,eval,fderiv_fun_add ((smooth a).differentiable (by simp) z)
        ((smooth b).differentiable (by simp) z),add_apply,ha,hb]
  | comp a b ha hb =>
      simp only [diff,eval_add,eval,fderiv_fun_mul ((smooth a).differentiable (by simp) z)
        ((smooth b).differentiable (by simp) z),add_apply,
        smul_apply,smul_eq_mul,ha,hb]
      ring
  | prec a b ha hb =>
      dsimp only [diff,eval]
      rw [atomDiff_eval]
      let v : Atom := data a
      have h := (Atom.profile_deriv v.2.2.2 ((v.2.1:ℝ)*coordinateLinear v.1 z+v.2.2.1)).comp_hasFDerivAt z
        (((coordinateLinear v.1).hasFDerivAt.const_mul (v.2.1:ℝ)).add_const (v.2.2.1:ℝ))
      change _ = fderiv ℝ (Atom.eval v) z (spacetimeBasis j)
      have hh : HasFDerivAt (Atom.eval v)
          (Atom.profileDerivative v.2.2.2 ((v.2.1:ℝ)*coordinateLinear v.1 z+v.2.2.1) •
            (v.2.1:ℝ) • coordinateLinear v.1) z := h
      rw [hh.fderiv]
      simp only [smul_apply,smul_eq_mul,coordinateLinear_basis]
      ring
  | rfind' a ha => simp [diff,eval]

theorem field_smooth (e : Fin 3 → Circuit) : Smooth (field e) :=
  contDiff_pi.mpr (fun j => smooth (e j))

theorem mixed_field (e : Fin 3 → Circuit) (α : List (Fin 4)) :
    mixedDerivative (field e) α = fun z j => eval (mixed (e j) α) z := by
  induction α with
  | nil => rfl
  | cons k α ih =>
      ext z j
      rw [mixedDerivative,ih]
      change (fderiv ℝ (fun z j => eval (mixed (e j) α) z) z (spacetimeBasis k)) j = _
      rw [fderiv_pi (fun i => (smooth (mixed (e i) α)).differentiable (by simp) z)]
      exact (diff_correct _ k z).symm

end Circuit
namespace JetExpr

end JetExpr
namespace BoxExpr

end BoxExpr
end Solenoidal

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.CircuitPrograms ----
namespace OAI

/-! SheetFlows circuit programs. -/

section
open Encodable Denumerable
namespace Solenoidal.Computing
open Nat.Partrec

end Solenoidal.Computing
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

namespace Circuit

theorem jetBound_nonneg (e : Fin 3 → Circuit) (a : List (Fin 4)) : 0 ≤ jetBound e a :=
  Finset.sum_nonneg (fun _ _ => bound_nonneg _ _)

theorem jetBound_correct (e : Fin 3 → Circuit) (a : List (Fin 4)) (z : SpaceTime)
    (hz : ∀ j, |coordinateLinear j z| ≤ 10) :
    ‖mixedDerivative (field e) a z‖ ≤ (jetBound e a : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast jetBound_nonneg e a)).mpr
  intro j
  rw [mixed_field]
  change |eval (mixed (e j) a) z| ≤ _
  apply (bound_correct _ 10 z (by simpa using hz)).trans
  exact_mod_cast Finset.single_le_sum (fun i _ => bound_nonneg _ _) (Finset.mem_univ j)

end Circuit

theorem circuit_periodic_jet {u : Field} (hu : Smooth u) (hx : SpatiallyPeriodic u)
    (ht : OnePeriodic u) {e : Fin 3 → Circuit}
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell)
    (a : List (Fin 4)) (z : SpaceTime) :
    mixedDerivative u a z = mixedDerivative (Circuit.field e) a (Int.fract z.1,wrapSpace z.2) := by
  have hp := periodic_field_reduction
    (mixedDerivative_spatially_periodic hu hx a) (mixedDerivative_onePeriodic hu ht a) z.1 z.2
  change mixedDerivative u a z = mixedDerivative u a (Int.fract z.1,wrapSpace z.2) at hp
  rw [hp]
  exact mixedDerivative_eqOn_cell hu (Circuit.field_smooth e) he a
    ⟨⟨Int.fract_nonneg _,(wrapSpace_mem z.2).1⟩,
      ⟨(Int.fract_lt_one _).le,(wrapSpace_mem z.2).2⟩⟩

theorem circuit_periodic_bound {u : Field} (hu : Smooth u) (hx : SpatiallyPeriodic u)
    (ht : OnePeriodic u) {e : Fin 3 → Circuit}
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell)
    (a : List (Fin 4)) (z : SpaceTime) :
    ‖mixedDerivative u a z‖ ≤ (Circuit.jetBound e a : ℝ) := by
  rw [circuit_periodic_jet hu hx ht he]
  apply Circuit.jetBound_correct
  intro j
  fin_cases j
  · change |Int.fract z.1| ≤ 10
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le.trans (by norm_num)
  all_goals
    change |wrapSpace z.2 _| ≤ 10
    rw [abs_of_nonneg ((wrapSpace_mem z.2).1 _)]
    exact (wrapSpace_mem z.2).2 _

namespace Computing

end Computing

namespace Computing

end Computing
end Solenoidal

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set Filter Encodable
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.circuit_periodic_bound := @_root_.OAI.Solenoidal.circuit_periodic_bound
