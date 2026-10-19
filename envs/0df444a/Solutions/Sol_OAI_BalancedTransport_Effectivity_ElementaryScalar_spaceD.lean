-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.ElementaryScalar.spaceD
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:13:45.827485+00:00
-- url     : https://prove2.me/submissions/c8d6cb50-765c-40ae-9fdd-616c0a44ab3f

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryCalculus.lean:L129-L154
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.ElementaryScalar.spaceD. The node keeps its source
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
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_differentiableAt
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_hasDerivAt

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericDifferentiation ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma dual_drop (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (q : List ℝ) :
    ((o.dual d k).realFrom x q).drop 5 = q := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, tag]

lemma dual_value (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 4 0 = o.real d x s := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, real, tag, rat, left, right, h]

lemma dual_differential (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 0 0 =
      o.differential d k (fun a => s.getD a 0) (fun a => q.getD (5*a) 0) := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.realFrom, real, differential, tag, rat, left, right,
      Nat.add_assoc, h, pow_two]
  change (((if Fin.ofNat d a = k then 1 else 0) : ℚ) : ℝ) =
    (if Fin.ofNat d a = k then 1 else 0)
  by_cases hh : Fin.ofNat d a = k <;>
    simp only [hh, ite_true, ite_false, Rat.cast_one, Rat.cast_zero]

lemma dual_valid (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : o.Valid s) :
    (o.dual d k).ValidFrom x q := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ValidFrom, Valid, real, tag, rat, left, right, h] at hv ⊢
  exact hv

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericScopes ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma realFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).realFrom x s = q.realFrom x (realFrom p x s) := List.foldl_append

lemma validFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).ValidFrom x s ↔ ValidFrom x p s ∧ q.ValidFrom x (realFrom p x s) := by
  induction p generalizing s with
  | nil => simp [ValidFrom, realFrom]
  | cons o p ih => simpa only [List.cons_append, ValidFrom, realFrom,
      List.foldl_cons, and_assoc] using and_congr_right (fun _ => ih _)

lemma scopedFrom_concat (p q : NumericProgram) (n : ℕ) :
    (p ++ q).ScopedFrom n ↔ p.ScopedFrom n ∧ q.ScopedFrom (n+p.length) := by
  induction p generalizing n with
  | nil => simp [ScopedFrom]
  | cons o p ih =>
    simp only [List.cons_append, ScopedFrom, List.length_cons]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1, and_assoc]

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericJets ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma dual_register (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s : List ℝ) (a : ℕ) :
    ((o.dual d k).realFrom x s).getD (5+a) 0 = s.getD a 0 := by
  have h := congrArg (fun l : List ℝ => l.getD a 0) (o.dual_drop d k x s)
  simpa [List.getD, List.getElem?_drop] using h

lemma dual_length (k : Fin d) (o : NumericOp) : (o.dual d k).length = 5 := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> rfl

lemma dual_scoped (k : Fin d) (o : NumericOp) {n : ℕ} (h : o.Scoped n) :
    (o.dual d k).ScopedFrom (5*n) := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ScopedFrom, Scoped, tag, left, right] at h ⊢
  all_goals omega

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma jetStep_length (k : Fin d) (p : NumericProgram) : (p.jetStep k).length = 5*p.length := by
  induction p with
  | nil => rfl
  | cons o p ih => simp only [jetStep, List.flatMap_cons, List.length_append,
      NumericOp.dual_length, List.length_cons] at ih ⊢; omega

lemma jetStep_scoped (k : Fin d) (p : NumericProgram) {n : ℕ} (h : p.ScopedFrom n) :
    (p.jetStep k).ScopedFrom (5*n) := by
  induction p generalizing n with
  | nil => trivial
  | cons o p ih =>
    rw [jetStep, List.flatMap_cons, scopedFrom_concat, NumericOp.dual_length]
    exact ⟨o.dual_scoped d k h.1, by simpa [jetStep, Nat.mul_add] using ih h.2⟩

lemma jetStep_closed (k : Fin d) (p : NumericProgram) (h : p.Closed) :
    (p.jetStep k).Closed := p.jetStep_scoped k h

lemma jetStep_validFrom (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ)
    (s q : List ℝ) (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : p.ValidFrom x s) :
    (p.jetStep k).ValidFrom x q ∧
      ∀ a, ((p.jetStep k).realFrom x q).getD (5*a+4) 0 = (p.realFrom x s).getD a 0 := by
  induction p generalizing s q with
  | nil => exact ⟨trivial, h⟩
  | cons o p ih =>
    have ho := o.dual_valid d k x s q h hv.1
    have hh (a : ℕ) : ((o.dual d k).realFrom x q).getD (5*a+4) 0 =
        (o.real d x s :: s).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k x s q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5,
          List.getD_cons_succ] using (o.dual_register d k x q (5*a+4)).trans (h a)
    have hi := ih _ _ hh hv.2
    refine ⟨?_, ?_⟩
    · exact (validFrom_concat _ _ x q).mpr ⟨ho, hi.1⟩
    · simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
        List.foldl_cons, List.foldl_append] using hi.2

lemma jetStep_valid (k : Fin d) (p : NumericProgram) {x : Fin d → ℝ} (hv : p.Valid x) :
    (p.jetStep k).Valid x := (p.jetStep_validFrom k x [] [] (by simp) hv).1

lemma jetStep_hasDerivAtFrom (k : Fin d) (p : NumericProgram)
    (x : ℝ → Fin d → ℝ) (s : ℝ → List ℝ) (q : List ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (h : ∀ a, q.getD (5*a+4) 0 = (s t).getD a 0)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (q.getD (5*a) 0) t)
    (hv : p.ValidFrom (x t) (s t)) :
    ∀ a, HasDerivAt (fun t => (p.realFrom (x t) (s t)).getD a 0)
      (((p.jetStep k).realFrom (x t) q).getD (5*a) 0) t := by
  induction p generalizing s q with
  | nil => exact hs
  | cons o p ih =>
    let s' : ℝ → List ℝ := fun v => o.real d (x v) (s v) :: s v
    let q' : List ℝ := (o.dual d k).realFrom (x t) q
    have hh (a : ℕ) : q'.getD (5*a+4) 0 = (s' t).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k (x t) (s t) q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5, s', q',
          List.getD_cons_succ] using (o.dual_register d k (x t) q (5*a+4)).trans (h a)
    have hd (a : ℕ) : HasDerivAt (fun v => (s' v).getD a 0) (q'.getD (5*a) 0) t := by
      cases a with
      | zero =>
        change HasDerivAt (fun v => o.real d (x v) (s v))
          (((o.dual d k).realFrom (x t) q).getD 0 0) t
        rw [o.dual_differential d k (x t) (s t) q h]
        exact o.hasDerivAt d k x s _ t hx hs hv.1
      | succ a =>
        change HasDerivAt (fun v => (s v).getD a 0)
          (((o.dual d k).realFrom (x t) q).getD (5*(a+1)) 0) t
        rw [show 5*(a+1)=5+5*a by omega, o.dual_register d k]
        exact hs a
    have hi := ih s' q' hh hd hv.2
    simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
      List.foldl_cons, List.foldl_append, s', q'] using hi

lemma differentiableAtFrom (p : NumericProgram) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : p.ValidFrom x (s x)) :
    ∀ a, DifferentiableAt ℝ (fun y => (p.realFrom y (s y)).getD a 0) x := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun y => o.real d y (s y) :: s y) ?_ hv.2
    intro a
    cases a with
    | zero => exact o.differentiableAt d x s hs hv.1
    | succ a => exact hs a

lemma differentiableAt (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    DifferentiableAt ℝ p.real x :=
  p.differentiableAtFrom x (fun _ => []) (fun _ => differentiableAt_const _) hv 0

lemma jetStep_real (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    (p.jetStep k).real x = fderiv ℝ p.real x (Pi.single k 1) := by
  let y : ℝ → Fin d → ℝ := fun t => x + t • Pi.single k 1
  have hy (i : Fin d) : HasDerivAt (fun t => y t i) (if i=k then 1 else 0) 0 := by
    have h := (hasDerivAt_const (0:ℝ) (x i)).add ((hasDerivAt_id (0:ℝ)).mul_const ((Pi.single k (1:ℝ) : Fin d → ℝ) i))
    simpa only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Function.const_apply, Pi.mul_apply, id_eq, mul_ite, mul_one, mul_zero, eq_comm, Pi.add_def, zero_add] using h
  have he : y 0 = x := by simp [y]
  have hh := p.jetStep_hasDerivAtFrom k y (fun _ => []) [] 0 hy (by simp)
    (by intro a; simpa using hasDerivAt_const (0:ℝ) (0:ℝ)) (by change p.Valid (y 0); rw [he]; exact hv) 0
  have hf := (p.differentiableAt x hv).hasFDerivAt.hasLineDerivAt (Pi.single k 1)
  exact HasDerivAt.unique (by simpa only [real, he, Nat.mul_zero] using hh) hf

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e] {f g : (Fin d → ℝ) → ℝ}

lemma differentiable (hf : Elementary f) : Differentiable ℝ f := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact fun x => p.differentiableAt x (hv x)

lemma coordinateDerivative (hf : Elementary f) (k : Fin d) :
    Elementary (fun x => fderiv ℝ f x (Pi.single k 1)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p.jetStep k, ?_, p.jetStep_closed k hc, fun x => p.jetStep_valid k (hv x), ?_⟩
  · apply List.length_pos_iff.mp
    rw [NumericProgram.jetStep_length]
    exact Nat.mul_pos (by decide) (List.length_pos_iff.mpr hn)
  · funext x
    exact p.jetStep_real k x (hv x)

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e]

end BalancedTransport.Effectivity.Elementary
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryCalculus ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
open BalancedTransport.Geometry

lemma congr {d : ℕ} [NeZero d] {f g : (Fin d → ℝ) → ℝ} (hf : Elementary f) (he : ∀x, f x = g x) : Elementary g := by
  rwa [← funext he]

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma fieldArgs_space_hasFDerivAt {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    HasFDerivAt (fun y => fieldArgs p t y)
      (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
        Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
          (fun _ => 0) k)) x := by
  apply hasFDerivAt_pi.mpr
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [fieldArgs] using hasFDerivAt_const t x
    · simpa [fieldArgs] using hasFDerivAt_apply i x
  · intro j
    simpa [fieldArgs] using hasFDerivAt_const (p j) x

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma spaceD (h : ElementaryScalar f) (i : Fin 3) : ElementaryScalar (fun p => BalancedTransport.spaceD i (f p)) := by
  have hd := h.coordinateDerivative (Fin.castAdd d i.succ)
  apply hd.congr
  intro z
  have hh := (h.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp (fieldSpace z) (fieldArgs_space_hasFDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  have hl : (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
        Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
          (fun _ => 0) k) : Space →L[ℝ] (Fin (4+d) → ℝ)) (Pi.single i 1) = Pi.single (Fin.castAdd d i.succ) 1 := by
    ext k
    refine Fin.addCases ?_ ?_ k
    · intro j
      refine Fin.cases ?_ (fun l => ?_) j
      · have hn : Fin.castAdd d (0 : Fin 4) ≠ Fin.castAdd d i.succ := by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
        simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_zero,
          zero_apply, Pi.single_apply, ite_eq_right hn]
      · simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_succ,
          ContinuousLinearMap.proj_apply, Pi.single_apply, Fin.castAdd_inj, Fin.succ_inj]
    · intro j
      have hn : Fin.natAdd 4 j ≠ Fin.castAdd d i.succ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ] at this; omega
      simp only [ContinuousLinearMap.pi_apply, Fin.addCases_right,
        zero_apply, Pi.single_apply, ite_eq_right hn]
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args, BalancedTransport.spaceD,
    ContinuousLinearMap.comp_apply, hl] using congrArg (fun l => l (Pi.single i 1)) he.fderiv.symm

end BalancedTransport.Effectivity.ElementaryScalar
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.ElementaryScalar.spaceD := @_root_.OAI.BalancedTransport.Effectivity.ElementaryScalar.spaceD
