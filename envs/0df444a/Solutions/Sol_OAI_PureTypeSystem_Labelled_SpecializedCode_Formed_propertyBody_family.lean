-- Prove2me | solution 1 for OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:21:17.556977+00:00
-- url     : https://prove2.me/submissions/a09a1ab8-bf23-4577-9550-334e0346b717

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_property_formula

section
-- module Solutions.OAIQ5_T6.TypeSystem_Labelled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Labelled beta reduction retains every annotation.
These are definitions, not an extension of the PTS specification. -/
namespace PureTypeSystem.Labelled

universe u

namespace Expr
variable {S : Type u}

theorem instantiate_rename (b a : Expr S) (ρ : Nat → Nat) :
    (b.rename (liftRen ρ)).instantiate (a.rename ρ) = (b.instantiate a).rename ρ := by
  simp only [instantiate, subst_rename, rename_subst]
  congr 1; funext n; cases n <;> rfl

end Expr

end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Wrappers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Concrete labelled term operations for wrappers. -/

/-! Finite simultaneous normal data witnesses.
Feasibility is semantic, so these lemmas do not assume a profile-generation
conjecture. The extra inhabitants are genuine fresh context variables. -/

namespace PureTypeSystem.Labelled

universe u
open Classical
variable {S : Type u} {P : Specification S}

namespace ProofWrapper

theorem apply_rename (R : ProofWrapper S) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename]

theorem apply_subst (R : ProofWrapper S) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst]

theorem rename_comp (R : ProofWrapper S) (ρ σ : Nat → Nat) :
    (R.rename σ).rename ρ = R.rename (ρ ∘ σ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp]

theorem instantiate_raise (R : ProofWrapper S) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single]

end ProofWrapper
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Logic
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}
namespace PositiveDataWrapper

theorem apply_rename (R : PositiveDataWrapper S) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename]
theorem inject_rename (R : PositiveDataWrapper S) (t : Expr S) (ρ : Nat → Nat) :
    (R.inject t).rename ρ = (R.rename ρ).inject (t.rename ρ) := by
  induction R <;> simp_all only [inject,rename,Expr.constLam_rename]
theorem project_rename (R : PositiveDataWrapper S) (w : Expr S) (ρ : Nat → Nat) :
    (R.project w).rename ρ = (R.rename ρ).project (w.rename ρ) := by
  induction R generalizing w <;> simp_all only [project,rename,Expr.rename]
theorem apply_subst (R : PositiveDataWrapper S) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst]
theorem inject_subst (R : PositiveDataWrapper S) (t : Expr S) (σ : Nat → Expr S) :
    (R.inject t).subst σ = (R.subst σ).inject (t.subst σ) := by
  induction R <;> simp_all only [inject,subst,Expr.constLam_subst]
theorem project_subst (R : PositiveDataWrapper S) (w : Expr S) (σ : Nat → Expr S) :
    (R.project w).subst σ = (R.subst σ).project (w.subst σ) := by
  induction R generalizing w <;> simp_all only [project,subst,Expr.subst]
theorem rename_comp (R : PositiveDataWrapper S) (ρ τ : Nat → Nat) :
    (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp]
theorem instantiate_raise (R : PositiveDataWrapper S) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {I J K : Set S} {R : PositiveDataWrapper S}
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode}
    (h : Formed W I J R) (e : Embedding P Γ γ Δ δ) : Formed (W.rename e) I J (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht

end Formed
end PositiveDataWrapper

namespace DataTail

theorem carrier_rename (U : DataTail S) (ρ : Nat → Nat) :
    U.carrier.rename ρ = (U.rename ρ).carrier := U.positive.apply_rename _ _
theorem send_rename (U : DataTail S) (Q : Expr S) (ρ : Nat → Nat) :
    (U.send Q).rename ρ = (U.rename ρ).send (Q.rename ρ) := by
  simp only [send,rename,PositiveDataWrapper.inject_rename,ProofWrapper.apply_rename]
theorem read_rename (U : DataTail S) (w : Expr S) (ρ : Nat → Nat) :
    (U.read w).rename ρ = (U.rename ρ).read (w.rename ρ) := by
  simp only [read,rename,PositiveDataWrapper.project_rename,ProofWrapper.apply_rename]
theorem carrier_subst (U : DataTail S) (σ : Nat → Expr S) :
    U.carrier.subst σ = (U.subst σ).carrier := U.positive.apply_subst _ _
theorem send_subst (U : DataTail S) (Q : Expr S) (σ : Nat → Expr S) :
    (U.send Q).subst σ = (U.subst σ).send (Q.subst σ) := by
  simp only [send,subst,PositiveDataWrapper.inject_subst,ProofWrapper.apply_subst]
theorem read_subst (U : DataTail S) (w : Expr S) (σ : Nat → Expr S) :
    (U.read w).subst σ = (U.subst σ).read (w.subst σ) := by
  simp only [read,subst,PositiveDataWrapper.project_subst,ProofWrapper.apply_subst]
theorem rename_comp (U : DataTail S) (ρ τ : Nat → Nat) :
    (U.rename τ).rename ρ = U.rename (ρ ∘ τ) := by
  cases U; simp only [rename,PositiveDataWrapper.rename_comp,ProofWrapper.rename_comp]
theorem instantiate_raise (U : DataTail S) (a : Expr S) :
    (U.rename Nat.succ).subst (Expr.single a) = U := by
  cases U; simp only [rename,subst,PositiveDataWrapper.instantiate_raise,ProofWrapper.instantiate_raise]

namespace Formed
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {J : Set S} {U : DataTail S}

theorem rename (h : Formed L J U) (e : Embedding P Γ γ Δ δ) :
    Formed (L.rename e) J (U.rename e.names) := by
  refine ⟨h.mem,h.nonempty,h.positive.rename e,h.encode.rename e,h.decode.rename e,?_⟩
  have hn (R : ProofWrapper S) : (R.rename e.names).containsNegative = R.containsNegative := by
    induction R <;> simp_all only [ProofWrapper.rename,ProofWrapper.containsNegative]
  exact (hn U.decode).trans h.negative

end Formed
end DataTail
end

section
universe u
variable {S : Type u}

namespace DataWrapper

theorem apply_rename {b} (R : DataWrapper S b) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename,DataTail.carrier_rename]
theorem apply_subst {b} (R : DataWrapper S b) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst,DataTail.carrier_subst]
theorem rename_comp {b} (R : DataWrapper S b) (ρ τ : Nat → Nat) :
    (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp,DataTail.rename_comp]
theorem instantiate_raise {b} (R : DataWrapper S b) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single,DataTail.instantiate_raise]

theorem argRen_comp (b : Bool) (ρ τ : Nat → Nat) :
    argRen b ρ ∘ argRen b τ = argRen b (ρ ∘ τ) := by
  cases b <;> funext n <;> cases n <;> rfl

theorem rename_build_observe {b} (R : DataWrapper S b) :
    (∀ T a ρ, (R.build T a).rename ρ = (R.rename ρ).build (T.rename ρ) (a.rename (argRen b ρ))) ∧
    (∀ T w a ρ, (R.observe T w a).rename ρ =
      (R.rename ρ).observe (T.rename ρ) (w.rename ρ) (a.rename (argRen (!b) ρ))) := by
  generalize he : R.depth = n
  induction n using Nat.strong_induction_on generalizing b R with
  | h n rec =>
   cases R with
   | identity =>
     constructor
     · intro T a ρ; simp only [build,rename,argRen,Bool.false_eq_true,ite_false, if_false]
     · intro T w a ρ
       simpa only [observe,rename,argRen,Bool.not_false,ite_true, if_true] using (Expr.instantiate_rename a w ρ).symm
   | positive R D e =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     exact ⟨fun T a ρ => by simp only [build,rename,Expr.constLam_rename,ih.1],
       fun T w a ρ => by simpa only [observe,rename,Expr.rename] using ih.2 T (.app .dd w e) a ρ⟩
   | @negative b R U =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     constructor
     · intro T a ρ
       simp only [build,Expr.rename,DataTail.send_rename,rename]
       rw [show (((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0) (a.rename (argRen (!b) Nat.succ))).rename (Expr.liftRen ρ)) =
         ((R.rename Nat.succ).rename (Expr.liftRen ρ)).observe ((T.rename Nat.succ).rename (Expr.liftRen ρ))
           ((Expr.var 0).rename (Expr.liftRen ρ)) ((a.rename (argRen (!b) Nat.succ)).rename (argRen (!b) (Expr.liftRen ρ))) from
         (rec R.depth (by simp only [← he,depth]; omega) (R.rename Nat.succ) (R.depth_rename Nat.succ)).2 _ _ _ _]
       simp only [apply_rename,rename_comp,DataTail.rename_comp,Expr.rename_comp,argRen_comp]
       have e : Expr.liftRen ρ ∘ Nat.succ = Nat.succ ∘ ρ := rfl
       rw [e]
       rfl
     · intro T w a ρ
       simp only [observe,rename,DataTail.read_rename,Expr.rename,ih.1,Bool.not_not]
end DataWrapper
end

universe u
variable {S : Type u} {P : Specification S}

namespace DataWrapper
namespace Formed

section
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {b : Bool} {R : DataWrapper S b}

theorem rename (h : Formed L I J R) (e : Embedding P Γ γ Δ δ) :
    Formed (L.rename e) I J (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht
  | negative h ht hU ih => exact ih.negative ht (hU.rename e)

end

end Formed

end DataWrapper
end PureTypeSystem.Labelled

/- A small finite compiler for the propositional term construction.
It has no type-theoretic assumptions. -/

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
namespace ProofWrapper
theorem subst_rename (R : ProofWrapper S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename]
theorem rename_subst (R : ProofWrapper S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst]
end ProofWrapper
namespace PositiveDataWrapper
theorem subst_rename (R : PositiveDataWrapper S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename]
theorem rename_subst (R : PositiveDataWrapper S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst]
end PositiveDataWrapper
namespace DataTail
theorem subst_rename (U : DataTail S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (U.rename ρ).subst σ = U.subst (σ ∘ ρ) := by
  cases U
  simp only [rename,subst,ProofWrapper.subst_rename,PositiveDataWrapper.subst_rename]
theorem rename_subst (U : DataTail S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (U.subst σ).rename ρ = U.subst (fun n => (σ n).rename ρ) := by
  cases U
  simp only [rename,subst,ProofWrapper.rename_subst,PositiveDataWrapper.rename_subst]
end DataTail
namespace DataWrapper

theorem subst_rename {b} (R : DataWrapper S b) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename,DataTail.subst_rename]
theorem rename_subst {b} (R : DataWrapper S b) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst,DataTail.rename_subst]

theorem argSub_shift (b : Bool) (σ : Nat → Expr S) :
    argSub b (Expr.liftSub σ) ∘ argRen b Nat.succ =
      fun n => (argSub b σ n).rename (argRen b Nat.succ) := by
  cases b
  · rfl
  · funext n
    cases n with
    | zero => rfl
    | succ n => simp only [argSub,argRen,ite_true, if_true,Function.comp_apply,Expr.liftRen,
        PureTypeSystem.Expr.liftRen,Expr.liftSub,Expr.rename_comp]; rfl

theorem subst_build_observe {b} (R : DataWrapper S b) :
    (∀ T a σ, (R.build T a).subst σ = (R.subst σ).build (T.subst σ) (a.subst (argSub b σ))) ∧
    (∀ T w a σ, (R.observe T w a).subst σ =
      (R.subst σ).observe (T.subst σ) (w.subst σ) (a.subst (argSub (!b) σ))) := by
  generalize he : R.depth = n
  induction n using Nat.strong_induction_on generalizing b R with
  | h n rec =>
   cases R with
   | identity =>
     constructor
     · intro T a σ; simp only [build,subst,argSub,Bool.false_eq_true,ite_false, if_false]
     · intro T w a σ
       simpa only [observe,subst,argSub,Bool.not_false,ite_true, if_true] using (Expr.instantiate_subst a w σ).symm
   | positive R D e =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     exact ⟨fun T a σ => by simp only [build,subst,Expr.constLam_subst,ih.1],
       fun T w a σ => by simpa only [observe,subst,Expr.subst] using ih.2 T (.app .dd w e) a σ⟩
   | @negative b R U =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     constructor
     · intro T a σ
       simp only [build,Expr.subst,DataTail.send_subst,subst]
       rw [(rec R.depth (by simp only [← he,depth]; omega) (R.rename Nat.succ) (R.depth_rename Nat.succ)).2]
       simp only [apply_subst,subst_rename,rename_subst,DataTail.subst_rename,DataTail.rename_subst,
         Expr.subst_rename,Expr.rename_subst,argSub_shift]
       rfl
     · intro T w a σ
       simp only [observe,subst,DataTail.read_subst,Expr.subst,ih.1,Bool.not_not]

end DataWrapper
end

universe u
variable {S : Type u} {P : Specification S}
namespace DataWrapper
theorem build_rename {b} (R : DataWrapper S b) (T a : Expr S) (ρ : Nat → Nat) :
    (R.build T a).rename ρ = (R.rename ρ).build (T.rename ρ) (a.rename (argRen b ρ)) :=
  R.rename_build_observe.1 T a ρ
theorem observe_rename {b} (R : DataWrapper S b) (T w a : Expr S) (ρ : Nat → Nat) :
    (R.observe T w a).rename ρ = (R.rename ρ).observe (T.rename ρ) (w.rename ρ) (a.rename (argRen (!b) ρ)) :=
  R.rename_build_observe.2 T w a ρ
theorem build_subst {b} (R : DataWrapper S b) (T a : Expr S) (σ : Nat → Expr S) :
    (R.build T a).subst σ = (R.subst σ).build (T.subst σ) (a.subst (argSub b σ)) :=
  R.subst_build_observe.1 T a σ
theorem observe_subst {b} (R : DataWrapper S b) (T w a : Expr S) (σ : Nat → Expr S) :
    (R.observe T w a).subst σ = (R.subst σ).observe (T.subst σ) (w.subst σ) (a.subst (argSub (!b) σ)) :=
  R.subst_build_observe.2 T w a σ
end DataWrapper
namespace Expr

theorem compose_rename (f g : Expr S) (ρ : Nat → Nat) :
    (f.compose g).rename (liftRen ρ) =
      (f.rename (liftRen ρ)).compose (g.rename (liftRen ρ)) := by
  simp only [compose,← instantiate_rename,rename_comp]
  congr 2
  funext n
  cases n <;> rfl
end Expr

namespace DataWrapper

theorem evalCallback_rename (R : DataWrapper S true) (T w : Expr S) (ρ : Nat → Nat) :
    (R.evalCallback T w).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalCallback (T.rename ρ) (w.rename ρ) := by
  simp only [evalCallback,observe_rename,rename_comp,Expr.rename_comp,
    argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem reencode_rename (R R' : DataWrapper S true) (T w : Expr S) (ρ : Nat → Nat) :
    (reencode R R' T w).rename ρ = reencode (R.rename ρ) (R'.rename ρ) (T.rename ρ) (w.rename ρ) := by
  simp only [reencode,build_rename,argRen,ite_true, if_true,evalCallback_rename]

end DataWrapper

namespace Expr
theorem compose_subst (f g : Expr S) (σ : Nat → Expr S) :
    (f.compose g).subst (liftSub σ) =
      (f.subst (liftSub σ)).compose (g.subst (liftSub σ)) := by
  simp only [compose,← instantiate_subst,subst_rename,rename_subst]
  congr 2
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [liftRen,PureTypeSystem.Expr.liftRen,liftSub,Function.comp_apply,rename_comp]; rfl

end Expr
namespace DataWrapper

theorem evalCallback_subst (R : DataWrapper S true) (T w : Expr S) (σ : Nat → Expr S) :
    (R.evalCallback T w).subst (Expr.liftSub σ) =
      (R.subst σ).evalCallback (T.subst σ) (w.subst σ) := by
  simp only [evalCallback,observe_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,argSub,Bool.not_true,Bool.false_eq_true,
    ite_false, if_false,Expr.subst,Expr.liftSub]
  rfl

theorem reencode_subst (R R' : DataWrapper S true) (T w : Expr S) (σ : Nat → Expr S) :
    (reencode R R' T w).subst σ = reencode (R.subst σ) (R'.subst σ) (T.subst σ) (w.subst σ) := by
  simp only [reencode,build_subst,argSub,ite_true, if_true,evalCallback_subst]

theorem reencodeBody_rename (R R' : DataWrapper S true) (T : Expr S) (ρ : Nat → Nat) :
    (reencodeBody R R' T).rename (Expr.liftRen ρ) =
      reencodeBody (R.rename ρ) (R'.rename ρ) (T.rename ρ) := by
  simp only [reencodeBody,reencode_rename,rename_comp,Expr.rename_comp,Expr.rename,
    Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

end DataWrapper

namespace LogicCode
variable (L : LogicCode S)

theorem rename_comp (ρ τ : Nat → Nat) : (L.rename τ).rename ρ = L.rename (ρ ∘ τ) := by
  cases L; simp only [rename,Expr.rename_comp,ProofWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (L.rename Nat.succ).subst (Expr.single a) = L := by
  cases L; simp only [rename,subst,Expr.subst_lift_single,ProofWrapper.instantiate_raise]

theorem imp_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.imp A B).rename ρ = (L.rename ρ).imp (A.rename ρ) (B.rename ρ) := by
  simp only [imp,ProofWrapper.apply_rename,Expr.arrow_rename,rename]
theorem imp_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.imp A B).subst σ = (L.subst σ).imp (A.subst σ) (B.subst σ) := by
  simp only [imp,ProofWrapper.apply_subst,Expr.arrow_subst,subst]
theorem neg_rename (A : Expr S) (ρ : Nat → Nat) :
    (L.neg A).rename ρ = (L.rename ρ).neg (A.rename ρ) := by
  simp only [neg,imp_rename,rename]
theorem neg_subst (A : Expr S) (σ : Nat → Expr S) :
    (L.neg A).subst σ = (L.subst σ).neg (A.subst σ) := by
  simp only [neg,imp_subst,subst]
theorem top_rename (ρ : Nat → Nat) : L.top.rename ρ = (L.rename ρ).top := by
  simp only [top,imp_rename,rename]
theorem top_subst (σ : Nat → Expr S) : L.top.subst σ = (L.subst σ).top := by
  simp only [top,imp_subst,subst]
theorem conj_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.conj A B).rename ρ = (L.rename ρ).conj (A.rename ρ) (B.rename ρ) := by
  simp only [conj,neg_rename,imp_rename]
theorem conj_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.conj A B).subst σ = (L.subst σ).conj (A.subst σ) (B.subst σ) := by
  simp only [conj,neg_subst,imp_subst]
theorem disj_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.disj A B).rename ρ = (L.rename ρ).disj (A.rename ρ) (B.rename ρ) := by
  simp only [disj,neg_rename,conj_rename]
theorem disj_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.disj A B).subst σ = (L.subst σ).disj (A.subst σ) (B.subst σ) := by
  simp only [disj,neg_subst,conj_subst]
theorem iff_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.iff A B).rename ρ = (L.rename ρ).iff (A.rename ρ) (B.rename ρ) := by
  simp only [iff,imp_rename,conj_rename]
theorem iff_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.iff A B).subst σ = (L.subst σ).iff (A.subst σ) (B.subst σ) := by
  simp only [iff,imp_subst,conj_subst]
theorem cond_rename (G A B : Expr S) (ρ : Nat → Nat) :
    (L.cond G A B).rename ρ = (L.rename ρ).cond (G.rename ρ) (A.rename ρ) (B.rename ρ) := by
  simp only [cond,conj_rename,disj_rename,neg_rename]
theorem cond_subst (G A B : Expr S) (σ : Nat → Expr S) :
    (L.cond G A B).subst σ = (L.subst σ).cond (G.subst σ) (A.subst σ) (B.subst σ) := by
  simp only [cond,conj_subst,disj_subst,neg_subst]
theorem sign_rename (b : Bool) (A : Expr S) (ρ : Nat → Nat) :
    (L.sign b A).rename ρ = (L.rename ρ).sign b (A.rename ρ) := by
  cases b <;> simp only [sign,ite_false, if_false,ite_true, if_true,Bool.false_eq_true,neg_rename]
theorem sign_subst (b : Bool) (A : Expr S) (σ : Nat → Expr S) :
    (L.sign b A).subst σ = (L.subst σ).sign b (A.subst σ) := by
  cases b <;> simp only [sign,ite_false, if_false,ite_true, if_true,Bool.false_eq_true,neg_subst]
end LogicCode

namespace DataWrapper

theorem contraCallback_rename (R : DataWrapper S true) (T t : Expr S) (ρ : Nat → Nat) :
    (R.contraCallback T t).rename (Expr.liftRen ρ) =
      (R.rename ρ).contraCallback (T.rename ρ) (t.rename ρ) := by
  simp only [contraCallback,observe_rename,rename_comp,Expr.rename_comp,
    argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem contraCallback_subst (R : DataWrapper S true) (T t : Expr S) (σ : Nat → Expr S) :
    (R.contraCallback T t).subst (Expr.liftSub σ) =
      (R.subst σ).contraCallback (T.subst σ) (t.subst σ) := by
  simp only [contraCallback,observe_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,argSub,Bool.not_true,Bool.false_eq_true,
    ite_false, if_false,Expr.subst,Expr.liftSub]
  rfl
end DataWrapper
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Channels
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace DoubleCode
variable (R : DoubleCode S)

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J K : Set S)
namespace Formed
variable {R L I J K}
theorem rename (h : Formed R L I J K) (e : Embedding P Γ γ Δ δ) :
    Formed (R.rename e.names) (L.rename e) I J K := ⟨h.first.rename e,h.second.rename e⟩
end Formed
end DoubleCode

namespace ChannelCode
variable (R : ChannelCode S)

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J K H : Set S)

namespace Formed
variable {R L I J K H}
theorem rename (h : Formed R L I J K H) (e : Embedding P Γ γ Δ δ) :
    Formed (R.rename e.names) (L.rename e) I J K H :=
  ⟨h.logical.rename e,h.raw.rename e,h.predicate.rename e⟩

end Formed
end ChannelCode

namespace LogicCode
variable (L : LogicCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (L.rename ρ).subst σ = L.subst (σ ∘ ρ) := by
  cases L; simp only [rename,subst,Expr.subst_rename,ProofWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (L.subst σ).rename ρ = L.subst (fun i => (σ i).rename ρ) := by
  cases L; simp only [rename,subst,Expr.rename_subst,ProofWrapper.rename_subst]
end LogicCode
namespace DoubleCode
variable (R : DoubleCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,DataWrapper.instantiate_raise]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun i => (σ i).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst]
theorem carrier_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.carrier T).rename ρ = (R.rename ρ).carrier (T.rename ρ) := by
  simp only [carrier,rename,DataWrapper.apply_rename]
theorem carrier_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.carrier T).subst σ = (R.subst σ).carrier (T.subst σ) := by
  simp only [carrier,subst,DataWrapper.apply_subst]
theorem emb_rename (L : LogicCode S) (b : Bool) (T t : Expr S) (ρ : Nat → Nat) :
    (R.emb L b T t).rename ρ = (R.rename ρ).emb (L.rename ρ) b (T.rename ρ) (t.rename ρ) := by
  simp only [emb,DataWrapper.build_rename,DataWrapper.apply_rename,DataWrapper.argRen,ite_true, if_true,
    LogicCode.sign_rename,LogicCode.rename_comp,DataWrapper.contraCallback_rename,rename]
  rfl
theorem emb_subst (L : LogicCode S) (b : Bool) (T t : Expr S) (σ : Nat → Expr S) :
    (R.emb L b T t).subst σ = (R.subst σ).emb (L.subst σ) b (T.subst σ) (t.subst σ) := by
  simp only [emb,DataWrapper.build_subst,DataWrapper.apply_subst,DataWrapper.argSub,ite_true, if_true,
    LogicCode.sign_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    DataWrapper.contraCallback_subst,subst]
  rfl
theorem eval_rename (T v Q : Expr S) (ρ : Nat → Nat) :
    (R.eval T v Q).rename ρ = (R.rename ρ).eval (T.rename ρ) (v.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [eval,DataWrapper.observe_rename,DataWrapper.build_rename,DataWrapper.apply_rename,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,rename]
theorem eval_subst (T v Q : Expr S) (σ : Nat → Expr S) :
    (R.eval T v Q).subst σ = (R.subst σ).eval (T.subst σ) (v.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [eval,DataWrapper.observe_subst,DataWrapper.build_subst,DataWrapper.apply_subst,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,subst]
theorem bit_rename (L : LogicCode S) (T v : Expr S) (ρ : Nat → Nat) :
    (R.bit L T v).rename ρ = (R.rename ρ).bit (L.rename ρ) (T.rename ρ) (v.rename ρ) := by
  change (R.eval T v (L.top.rename Nat.succ)).rename ρ = _
  rw [eval_rename,Expr.rename_comp]
  change _ = (R.rename ρ).eval _ _ ((L.rename ρ).top.rename Nat.succ)
  rw [← LogicCode.top_rename,Expr.rename_comp]
  rfl
theorem bit_subst (L : LogicCode S) (T v : Expr S) (σ : Nat → Expr S) :
    (R.bit L T v).subst σ = (R.subst σ).bit (L.subst σ) (T.subst σ) (v.subst σ) := by
  change (R.eval T v (L.top.rename Nat.succ)).subst σ = _
  rw [eval_subst,Expr.subst_rename]
  change _ = (R.subst σ).eval _ _ ((L.subst σ).top.rename Nat.succ)
  rw [← LogicCode.top_subst,Expr.rename_subst]
  rfl
theorem rec_rename (L : LogicCode S) (T v Q : Expr S) (ρ : Nat → Nat) :
    (R.recover L T v Q).rename ρ = (R.rename ρ).recover (L.rename ρ) (T.rename ρ) (v.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [recover,LogicCode.cond_rename,LogicCode.neg_rename,bit_rename,eval_rename]
theorem rec_subst (L : LogicCode S) (T v Q : Expr S) (σ : Nat → Expr S) :
    (R.recover L T v Q).subst σ = (R.subst σ).recover (L.subst σ) (T.subst σ) (v.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [recover,LogicCode.cond_subst,LogicCode.neg_subst,bit_subst,eval_subst]

theorem bitBody_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.bitBody L T).rename (Expr.liftRen ρ) = (R.rename ρ).bitBody (L.rename ρ) (T.rename ρ) := by
  simp only [bitBody,bit_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  rfl
theorem recBody_rename (L : LogicCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.recBody L T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).recBody (L.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [recBody,rec_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  congr 1
  congr 1
  funext n; cases n <;> rfl

theorem tower_rename (n : Nat) (T : Expr S) (ρ : Nat → Nat) :
    (R.tower n T).rename ρ = (R.rename ρ).tower n (T.rename ρ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower,carrier_rename,ih]
theorem tower_subst (n : Nat) (T : Expr S) (σ : Nat → Expr S) :
    (R.tower n T).subst σ = (R.subst σ).tower n (T.subst σ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower,carrier_subst,ih]
theorem embed_rename (L : LogicCode S) (bs : List Bool) (T t : Expr S) (ρ : Nat → Nat) :
    (R.embed L bs T t).rename ρ = (R.rename ρ).embed (L.rename ρ) bs (T.rename ρ) (t.rename ρ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [embed,emb_rename,tower_rename,ih]
theorem embed_subst (L : LogicCode S) (bs : List Bool) (T t : Expr S) (σ : Nat → Expr S) :
    (R.embed L bs T t).subst σ = (R.subst σ).embed (L.subst σ) bs (T.subst σ) (t.subst σ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [embed,emb_subst,tower_subst,ih]
theorem recoveryBody_rename (L : LogicCode S) (n : Nat) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.recoveryBody L n T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).recoveryBody (L.rename ρ) n (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recoveryBody,recBody_rename,tower_rename,ih]
theorem tagBody_rename (L : LogicCode S) (bs : List Bool) (T : Expr S) (ρ : Nat → Nat) :
    (R.tagBody L bs T).rename (Expr.liftRen ρ) =
      (R.rename ρ).tagBody (L.rename ρ) bs (T.rename ρ) := by
  induction bs with
  | nil =>
    simp only [tagBody,Expr.rename_comp,← LogicCode.top_rename]
    rfl
  | cons b bs ih =>
    simp only [tagBody,LogicCode.conj_rename,LogicCode.sign_rename,LogicCode.rename_comp,
      bitBody_rename,recBody_rename,tower_rename,ih]
    rfl

end DoubleCode

namespace DoubleCode
variable (R : DoubleCode S)

theorem tagged_rename (L : LogicCode S) (q : Fin 9) (T t : Expr S) (ρ : Nat → Nat) :
    (R.tagged L q T t).rename ρ = (R.rename ρ).tagged (L.rename ρ) q (T.rename ρ) (t.rename ρ) :=
  R.embed_rename L (queryBits q) T t ρ
theorem tagged_subst (L : LogicCode S) (q : Fin 9) (T t : Expr S) (σ : Nat → Expr S) :
    (R.tagged L q T t).subst σ = (R.subst σ).tagged (L.subst σ) q (T.subst σ) (t.subst σ) :=
  R.embed_subst L (queryBits q) T t σ

theorem encodeBody_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (ρ : Nat → Nat) :
    (R.encodeBody U L t T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).encodeBody (U.rename ρ) (L.rename ρ) t (T.rename ρ) (p.rename ρ) := by
  simp only [encodeBody,LogicCode.disj_rename,LogicCode.conj_rename,tagBody_rename,
    recoveryBody_rename,DataWrapper.evalCallback_rename,LogicCode.rename_comp]
  rfl

theorem embedBody_rename (L : LogicCode S) (q : Fin 9) (T : Expr S) (ρ : Nat → Nat) :
    (R.embedBody L q T).rename (Expr.liftRen ρ) = (R.rename ρ).embedBody (L.rename ρ) q (T.rename ρ) := by
  simp only [embedBody,tagged_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  rfl

end DoubleCode

namespace ProbeCode
variable (R : ProbeCode S)

theorem doubled_rename (ρ : Nat → Nat) : (R.rename ρ).doubled = R.doubled.rename ρ := rfl
theorem doubled_subst (σ : Nat → Expr S) : (R.subst σ).doubled = R.doubled.subst σ := rfl

theorem rawType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.rawType A).rename ρ = (R.rename ρ).rawType (A.rename ρ) := by
  simp only [rawType,rename,DataWrapper.apply_rename]
theorem rawType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.rawType A).subst σ = (R.subst σ).rawType (A.subst σ) := by
  simp only [rawType,subst,DataWrapper.apply_subst]
theorem paramType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.paramType A).rename ρ = (R.rename ρ).paramType (A.rename ρ) := by
  simp only [paramType,DoubleCode.paramType,DoubleCode.bpType,DoubleCode.big,
    DataWrapper.apply_rename,DoubleCode.tower_rename,rawType_rename,doubled,rename,DoubleCode.rename]
theorem paramType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.paramType A).subst σ = (R.subst σ).paramType (A.subst σ) := by
  simp only [paramType,DoubleCode.paramType,DoubleCode.bpType,DoubleCode.big,
    DataWrapper.apply_subst,DoubleCode.tower_subst,rawType_subst,doubled,subst,DoubleCode.subst]
theorem singleType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.singleType A).rename ρ = (R.rename ρ).singleType (A.rename ρ) := by
  simp only [singleType,DoubleCode.carrier_rename,paramType_rename,doubled_rename]
theorem singleType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.singleType A).subst σ = (R.subst σ).singleType (A.subst σ) := by
  simp only [singleType,DoubleCode.carrier_subst,paramType_subst,doubled_subst]
theorem funType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.funType A).rename ρ = (R.rename ρ).funType (A.rename ρ) := by
  simp only [funType,Expr.arrow_rename,singleType_rename,DataTail.carrier_rename,rename]
theorem funType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.funType A).subst σ = (R.subst σ).funType (A.subst σ) := by
  simp only [funType,Expr.arrow_subst,singleType_subst,DataTail.carrier_subst,subst]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R
  simp only [rename,subst,DataWrapper.instantiate_raise,PositiveDataWrapper.instantiate_raise,
    DataTail.instantiate_raise]

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  (L : LogicSetup P Γ γ C) (I J k p n g : Set S)

namespace Formed
variable {R L I J k p n g} (h : R.Formed L I J k p n g)
include h
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (R.rename e.names).Formed (L.rename e) I J k p n g :=
  ⟨h.mainTriple,h.funTriple,h.ax,h.initial.rename e,h.raw.rename e,h.back.rename e,
    h.funPath.rename e,h.lifting.rename e,h.tail.rename e⟩
end Formed
end ProbeCode

end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
namespace ChannelCode
variable (R : ChannelCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp]
theorem logicalType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.logicalType T).rename ρ = (R.rename ρ).logicalType (T.rename ρ) := by
  simp only [logicalType,rename,DataWrapper.apply_rename]
theorem logicalType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.logicalType T).subst σ = (R.subst σ).logicalType (T.subst σ) := by
  simp only [logicalType,subst,DataWrapper.apply_subst]
theorem rawType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.rawType T).rename ρ = (R.rename ρ).rawType (T.rename ρ) := by
  simp only [rawType,rename,DataWrapper.apply_rename]
theorem rawType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.rawType T).subst σ = (R.subst σ).rawType (T.subst σ) := by
  simp only [rawType,subst,DataWrapper.apply_subst]
theorem predicateType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.predicateType T).rename ρ = (R.rename ρ).predicateType (T.rename ρ) := by
  simp only [predicateType,rename,DataWrapper.apply_rename]
theorem predicateType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.predicateType T).subst σ = (R.subst σ).predicateType (T.subst σ) := by
  simp only [predicateType,subst,DataWrapper.apply_subst]
theorem toRaw_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.toRaw T y).rename ρ = (R.rename ρ).toRaw (T.rename ρ) (y.rename ρ) := by
  simp only [toRaw,DataWrapper.reencode_rename,rename]
theorem toRaw_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.toRaw T y).subst σ = (R.subst σ).toRaw (T.subst σ) (y.subst σ) := by
  simp only [toRaw,DataWrapper.reencode_subst,subst]
theorem toLog_rename (T c : Expr S) (ρ : Nat → Nat) :
    (R.toLog T c).rename ρ = (R.rename ρ).toLog (T.rename ρ) (c.rename ρ) := by
  simp only [toLog,DataWrapper.reencode_rename,rename]
theorem toLog_subst (T c : Expr S) (σ : Nat → Expr S) :
    (R.toLog T c).subst σ = (R.subst σ).toLog (T.subst σ) (c.subst σ) := by
  simp only [toLog,DataWrapper.reencode_subst,subst]
theorem round_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.round T y).rename ρ = (R.rename ρ).round (T.rename ρ) (y.rename ρ) := by
  simp only [round,toRaw_rename,toLog_rename]
theorem round_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.round T y).subst σ = (R.subst σ).round (T.subst σ) (y.subst σ) := by
  simp only [round,toRaw_subst,toLog_subst]
theorem eval_rename (T p y : Expr S) (ρ : Nat → Nat) :
    (R.eval T p y).rename ρ = (R.rename ρ).eval (T.rename ρ) (p.rename ρ) (y.rename ρ) := by
  simp only [eval,DataWrapper.observe_rename,rawType_rename,toRaw_rename,rename,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
theorem eval_subst (T p y : Expr S) (σ : Nat → Expr S) :
    (R.eval T p y).subst σ = (R.subst σ).eval (T.subst σ) (p.subst σ) (y.subst σ) := by
  simp only [eval,DataWrapper.observe_subst,rawType_subst,toRaw_subst,subst,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
end ChannelCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace QuantifierCode
variable (K : QuantifierCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (K.rename τ).rename ρ = K.rename (ρ ∘ τ) := by
  cases K; simp only [rename,ProofWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (K.rename Nat.succ).subst (Expr.single a) = K := by
  cases K; simp only [rename,subst,ProofWrapper.instantiate_raise]
theorem all_rename (T Q : Expr S) (ρ : Nat → Nat) :
    (K.all T Q).rename ρ = (K.rename ρ).all (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [all,rename,ProofWrapper.apply_rename,Expr.rename,ProofWrapper.rename_comp]
  rfl
theorem all_subst (T Q : Expr S) (σ : Nat → Expr S) :
    (K.all T Q).subst σ = (K.subst σ).all (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [all,subst,ProofWrapper.apply_subst,Expr.subst,ProofWrapper.subst_rename,ProofWrapper.rename_subst]
  rfl
end QuantifierCode
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace Expr
theorem lifted_comp (ρ τ : Nat → Nat) : liftRen ρ ∘ liftRen τ = liftRen (ρ ∘ τ) := by
  funext n; cases n <;> rfl

end Expr
namespace LogicCode
variable (L : LogicCode S)
theorem guardBody_rename (G Q : Expr S) (ρ : Nat → Nat) :
    (L.guardBody G Q).rename (Expr.liftRen ρ) =
      (L.rename ρ).guardBody (G.rename (Expr.liftRen ρ)) (Q.rename (Expr.liftRen ρ)) := by
  simp only [guardBody,imp_rename,rename_comp]
  rfl
theorem guardAll_rename (K : QuantifierCode S) (T G Q : Expr S) (ρ : Nat → Nat) :
    (L.guardAll K T G Q).rename ρ =
      (L.rename ρ).guardAll (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (Q.rename (Expr.liftRen ρ)) := by
  simp only [guardAll,QuantifierCode.all_rename,guardBody_rename]
end LogicCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Relations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace ChannelCode
variable (R : ChannelCode S)

theorem evalPredBody_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.evalPredBody T y).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalPredBody (T.rename ρ) (y.rename ρ) := by
  simp only [evalPredBody,eval_rename,rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem compareBody_rename (L : LogicCode S) (T y z : Expr S) (ρ : Nat → Nat) :
    (R.compareBody L T y z).rename (Expr.liftRen ρ) =
      (R.rename ρ).compareBody (L.rename ρ) (T.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compareBody,LogicCode.iff_rename,LogicCode.rename_comp,evalPredBody_rename]
  rfl

theorem relation_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.relation L K T G y z).rename ρ =
      (R.rename ρ).relation (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [relation,LogicCode.guardAll_rename,predicateType_rename,compareBody_rename]

end ChannelCode

namespace ChannelCode
variable (R : ChannelCode S)

theorem roundRespectBody_rename (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.roundRespectBody L T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).roundRespectBody (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [roundRespectBody,LogicCode.iff_rename,eval_rename,round_rename,rename_comp,
    LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem roundRespect_rename (L : LogicCode S) (K : QuantifierCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.roundRespect L K T p).rename ρ =
      (R.rename ρ).roundRespect (L.rename ρ) (K.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [roundRespect,QuantifierCode.all_rename,logicalType_rename,roundRespectBody_rename]

theorem roundRespectBody_subst (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.roundRespectBody L T p).subst (Expr.liftSub σ) =
      (R.subst σ).roundRespectBody (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [roundRespectBody,LogicCode.iff_subst,eval_subst,round_subst,subst,rename,
    LogicCode.subst,LogicCode.rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.subst,Expr.liftSub]
  rfl

theorem roundRespect_subst (L : LogicCode S) (K : QuantifierCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.roundRespect L K T p).subst σ =
      (R.subst σ).roundRespect (L.subst σ) (K.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [roundRespect,QuantifierCode.all_subst,logicalType_subst,roundRespectBody_subst]

theorem goodBody_rename (L : LogicCode S) (K : QuantifierCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.goodBody L K T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).goodBody (L.rename ρ) (K.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [goodBody,LogicCode.conj_rename,roundRespect_rename,rename_comp,LogicCode.rename_comp,
    QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

end ChannelCode

namespace LogicCode
variable (L : LogicCode S)
theorem guardBody_subst (G Q : Expr S) (σ : Nat → Expr S) :
    (L.guardBody G Q).subst (Expr.liftSub σ) =
      (L.subst σ).guardBody (G.subst (Expr.liftSub σ)) (Q.subst (Expr.liftSub σ)) := by
  simp only [guardBody,imp_subst,subst,rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem guardAll_subst (K : QuantifierCode S) (T G Q : Expr S) (σ : Nat → Expr S) :
    (L.guardAll K T G Q).subst σ =
      (L.subst σ).guardAll (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (Q.subst (Expr.liftSub σ)) := by
  simp only [guardAll,QuantifierCode.all_subst,guardBody_subst]
end LogicCode
namespace ChannelCode
variable (R : ChannelCode S)
theorem evalPredBody_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.evalPredBody T y).subst (Expr.liftSub σ) =
      (R.subst σ).evalPredBody (T.subst σ) (y.subst σ) := by
  simp only [evalPredBody,eval_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem compareBody_subst (L : LogicCode S) (T y z : Expr S) (σ : Nat → Expr S) :
    (R.compareBody L T y z).subst (Expr.liftSub σ) =
      (R.subst σ).compareBody (L.subst σ) (T.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compareBody,LogicCode.iff_subst,evalPredBody_subst,LogicCode.subst,LogicCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem relation_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.relation L K T G y z).subst σ =
      (R.subst σ).relation (L.subst σ) (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [relation,LogicCode.guardAll_subst,predicateType_subst,compareBody_subst]

theorem classBody_rename (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (ρ : Nat → Nat) :
    (R.classBody L K T G y).rename (Expr.liftRen ρ) =
      (R.rename ρ).classBody (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) := by
  simp only [classBody,relation_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

end ChannelCode

namespace LogicCode
variable (L : LogicCode S)
theorem negBody_rename (Q : Expr S) (ρ : Nat → Nat) :
    (L.negBody Q).rename (Expr.liftRen ρ) = (L.rename ρ).negBody (Q.rename (Expr.liftRen ρ)) := by
  simp only [negBody,neg_rename,rename_comp]
  rfl
theorem negBody_subst (Q : Expr S) (σ : Nat → Expr S) :
    (L.negBody Q).subst (Expr.liftSub σ) = (L.subst σ).negBody (Q.subst (Expr.liftSub σ)) := by
  simp only [negBody,neg_subst,subst,rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem ex_rename (K : QuantifierCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (L.ex K T Q).rename ρ = (L.rename ρ).ex (K.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [ex,neg_rename,QuantifierCode.all_rename,negBody_rename]
theorem ex_subst (K : QuantifierCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (L.ex K T Q).subst σ = (L.subst σ).ex (K.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [ex,neg_subst,QuantifierCode.all_subst,negBody_subst]
end LogicCode

namespace ChannelCode
variable (R : ChannelCode S)
theorem pred_rename (T Q : Expr S) (ρ : Nat → Nat) :
    (R.pred T Q).rename ρ = (R.rename ρ).pred (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [pred,DataWrapper.build_rename,rawType_rename,Expr.compose_rename,
    DataWrapper.reencodeBody_rename,DataWrapper.argRen,ite_true, if_true,rename]

theorem evalBody_rename (T p : Expr S) (ρ : Nat → Nat) :
    (R.evalBody T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalBody (T.rename ρ) (p.rename ρ) := by
  simp only [evalBody,eval_rename,rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem evalBody_subst (T p : Expr S) (σ : Nat → Expr S) :
    (R.evalBody T p).subst (Expr.liftSub σ) = (R.subst σ).evalBody (T.subst σ) (p.subst σ) := by
  simp only [evalBody,eval_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem predCompareBody_rename (L : LogicCode S) (T p q : Expr S) (ρ : Nat → Nat) :
    (R.predCompareBody L T p q).rename (Expr.liftRen ρ) =
      (R.rename ρ).predCompareBody (L.rename ρ) (T.rename ρ) (p.rename ρ) (q.rename ρ) := by
  simp only [predCompareBody,LogicCode.iff_rename,LogicCode.rename_comp,evalBody_rename]
  rfl
theorem predCompareBody_subst (L : LogicCode S) (T p q : Expr S) (σ : Nat → Expr S) :
    (R.predCompareBody L T p q).subst (Expr.liftSub σ) =
      (R.subst σ).predCompareBody (L.subst σ) (T.subst σ) (p.subst σ) (q.subst σ) := by
  simp only [predCompareBody,LogicCode.iff_subst,evalBody_subst,LogicCode.subst,LogicCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem predCompare_rename (L : LogicCode S) (K : QuantifierCode S) (T p q : Expr S) (ρ : Nat → Nat) :
    (R.predCompare L K T p q).rename ρ =
      (R.rename ρ).predCompare (L.rename ρ) (K.rename ρ) (T.rename ρ) (p.rename ρ) (q.rename ρ) := by
  simp only [predCompare,QuantifierCode.all_rename,logicalType_rename,predCompareBody_rename]
theorem predCompare_subst (L : LogicCode S) (K : QuantifierCode S) (T p q : Expr S) (σ : Nat → Expr S) :
    (R.predCompare L K T p q).subst σ =
      (R.subst σ).predCompare (L.subst σ) (K.subst σ) (T.subst σ) (p.subst σ) (q.subst σ) := by
  simp only [predCompare,QuantifierCode.all_subst,logicalType_subst,predCompareBody_subst]
end ChannelCode

namespace ChannelCode
variable (R : ChannelCode S)
theorem classPred_rename (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (ρ : Nat → Nat) :
    (R.classPred L K T G y).rename ρ =
      (R.rename ρ).classPred (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) := by
  simp only [classPred,pred_rename,classBody_rename]
theorem unionBody_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.unionBody L K T G y z).rename (Expr.liftRen ρ) =
      (R.rename ρ).unionBody (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [unionBody,LogicCode.disj_rename,LogicCode.rename_comp,classBody_rename]
  rfl
theorem unionPred_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.unionPred L K T G y z).rename ρ =
      (R.rename ρ).unionPred (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [unionPred,pred_rename,unionBody_rename]
end ChannelCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Pairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}
namespace DataWrapper
theorem reencodeBody_subst (R R' : DataWrapper S true) (T : Expr S) (σ : Nat → Expr S) :
    (reencodeBody R R' T).subst (Expr.liftSub σ) =
      reencodeBody (R.subst σ) (R'.subst σ) (T.subst σ) := by
  simp only [reencodeBody,reencode_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
end DataWrapper
namespace Expr
theorem liftSub_succ_natural (σ : Nat → Expr S) :
    liftSub (liftSub σ) ∘ liftRen Nat.succ =
      (fun n => (liftSub σ n).rename (liftRen Nat.succ)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp_apply,liftSub,liftRen,PureTypeSystem.Expr.liftRen,rename_comp]
    rfl
end Expr
namespace ChannelCode
variable (R : ChannelCode S)
theorem pred_subst (T Q : Expr S) (σ : Nat → Expr S) :
    (R.pred T Q).subst σ = (R.subst σ).pred (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [pred,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,
    Expr.compose_subst,DataWrapper.reencodeBody_subst,rawType_subst,subst]

theorem classBody_subst (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (σ : Nat → Expr S) :
    (R.classBody L K T G y).subst (Expr.liftSub σ) =
      (R.subst σ).classBody (L.subst σ) (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (y.subst σ) := by
  simp only [classBody,relation_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.liftSub_succ_natural,Expr.liftSub,Expr.subst]
  rfl

theorem classPred_subst (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (σ : Nat → Expr S) :
    (R.classPred L K T G y).subst σ = (R.subst σ).classPred (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) := by
  simp only [classPred,pred_subst,classBody_subst]
theorem unionBody_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.unionBody L K T G y z).subst (Expr.liftSub σ) = (R.subst σ).unionBody (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [unionBody,LogicCode.disj_subst,classBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem unionPred_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.unionPred L K T G y z).subst σ = (R.subst σ).unionPred (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [unionPred,pred_subst,unionBody_subst]

theorem isClass_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) (ρ : Nat → Nat) :
    (R.isClass L KP T G Q t y).rename ρ = (R.rename ρ).isClass (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) t (y.rename ρ) := by
  simp only [isClass,← Expr.instantiate_rename,classPred_rename]
theorem isClass_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) (σ : Nat → Expr S) :
    (R.isClass L KP T G Q t y).subst σ = (R.subst σ).isClass (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) t (y.subst σ) := by
  simp only [isClass,← Expr.instantiate_subst,classPred_subst]
theorem edge_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) (ρ : Nat → Nat) :
    (R.edge L KP T G Q t y z).rename ρ = (R.rename ρ).edge (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) t (y.rename ρ) (z.rename ρ) := by
  simp only [edge,LogicCode.conj_rename,isClass_rename,← Expr.instantiate_rename,unionPred_rename]
theorem edge_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) (σ : Nat → Expr S) :
    (R.edge L KP T G Q t y z).subst σ = (R.subst σ).edge (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) t (y.subst σ) (z.subst σ) := by
  simp only [edge,LogicCode.conj_subst,isClass_subst,← Expr.instantiate_subst,unionPred_subst]

theorem formExBody_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) (ρ : Nat → Nat) :
    (R.formExBody L KP T G Q p z).rename (Expr.liftRen ρ) = (R.rename ρ).formExBody (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) (p.rename ρ) (z.rename ρ) := by
  simp only [formExBody,LogicCode.conj_rename,LogicCode.rename_comp,edge_rename,eval_rename,
    rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem formExBody_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) (σ : Nat → Expr S) :
    (R.formExBody L KP T G Q p z).subst (Expr.liftSub σ) = (R.subst σ).formExBody (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) (p.subst σ) (z.subst σ) := by
  simp only [formExBody,LogicCode.conj_subst,edge_subst,eval_subst,subst,rename,
    DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.liftSub_succ_natural,Expr.subst,Expr.liftSub]
  rfl

theorem pairForm_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) (ρ : Nat → Nat) :
    (R.pairForm L KY KP T G Q p a z).rename ρ = (R.rename ρ).pairForm (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) (z.rename ρ) := by
  simp only [pairForm,LogicCode.disj_rename,LogicCode.ex_rename,logicalType_rename,formExBody_rename,edge_rename]
theorem pairForm_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) (σ : Nat → Expr S) :
    (R.pairForm L KY KP T G Q p a z).subst σ = (R.subst σ).pairForm (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) (z.subst σ) := by
  simp only [pairForm,LogicCode.disj_subst,LogicCode.ex_subst,logicalType_subst,formExBody_subst,edge_subst]
theorem pairBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (ρ : Nat → Nat) :
    (R.pairBody L KY KP T G Q p a).rename (Expr.liftRen ρ) = (R.rename ρ).pairBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) := by
  simp only [pairBody,pairForm_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem pairBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (σ : Nat → Expr S) :
    (R.pairBody L KY KP T G Q p a).subst (Expr.liftSub σ) = (R.subst σ).pairBody (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) := by
  simp only [pairBody,pairForm_subst,subst,rename,
    DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.liftSub_succ_natural,Expr.subst,Expr.liftSub]
  rfl
theorem pairPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (ρ : Nat → Nat) :
    (R.pairPred L KY KP T G Q p a).rename ρ = (R.rename ρ).pairPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) := by
  simp only [pairPred,pred_rename,pairBody_rename]
theorem pairPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (σ : Nat → Expr S) :
    (R.pairPred L KY KP T G Q p a).subst σ = (R.subst σ).pairPred (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) := by
  simp only [pairPred,pred_subst,pairBody_subst]
end ChannelCode

namespace DoubleCode
variable (R : DoubleCode S)
theorem bitBody_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.bitBody L T).subst (Expr.liftSub σ) =
      (R.subst σ).bitBody (L.subst σ) (T.subst σ) := by
  simp only [bitBody,bit_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl

theorem recBody_subst (L : LogicCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.recBody L T Q).subst (Expr.liftSub σ) =
      (R.subst σ).recBody (L.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [recBody,rec_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  congr 1
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp_apply,Expr.liftSub,Expr.liftRen,PureTypeSystem.Expr.liftRen,Expr.rename_comp]
    congr 1

theorem recoveryBody_subst (L : LogicCode S) (n : Nat) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.recoveryBody L n T Q).subst (Expr.liftSub σ) =
      (R.subst σ).recoveryBody (L.subst σ) n (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recoveryBody,recBody_subst,tower_subst,ih]
theorem tagBody_subst (L : LogicCode S) (bs : List Bool) (T : Expr S) (σ : Nat → Expr S) :
    (R.tagBody L bs T).subst (Expr.liftSub σ) =
      (R.subst σ).tagBody (L.subst σ) bs (T.subst σ) := by
  induction bs with
  | nil =>
    simp only [tagBody,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
    rfl
  | cons b bs ih =>
    simp only [tagBody,LogicCode.conj_subst,LogicCode.sign_subst,LogicCode.subst_rename,
      LogicCode.rename_subst,bitBody_subst,recBody_subst,tower_subst,ih]
    rfl

theorem big_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.big T).rename ρ = (R.rename ρ).big (T.rename ρ) := R.tower_rename 4 T ρ
theorem big_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.big T).subst σ = (R.subst σ).big (T.subst σ) := R.tower_subst 4 T σ
theorem bpType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.bpType T).rename ρ = (R.rename ρ).bpType (T.rename ρ) := by
  simp only [bpType,DataWrapper.apply_rename,big_rename]; rfl
theorem bpType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.bpType T).subst σ = (R.subst σ).bpType (T.subst σ) := by
  simp only [bpType,DataWrapper.apply_subst,big_subst]; rfl

theorem embedBody_subst (L : LogicCode S) (q : Fin 9) (T : Expr S) (σ : Nat → Expr S) :
    (R.embedBody L q T).subst (Expr.liftSub σ) =
      (R.subst σ).embedBody (L.subst σ) q (T.subst σ) := by
  simp only [embedBody,tagged_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl

theorem decoderBody_rename (L : LogicCode S) (T bp : Expr S) (ρ : Nat → Nat) :
    (R.decoderBody L T bp).rename (Expr.liftRen ρ) =
      (R.rename ρ).decoderBody (L.rename ρ) (T.rename ρ) (bp.rename ρ) := by
  simp only [decoderBody,Expr.compose_rename,DataWrapper.evalCallback_rename,embedBody_rename,big_rename]
  rfl

theorem decode_rename (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) (ρ : Nat → Nat) :
    (R.decode U L T bp).rename ρ =
      (R.rename ρ).decode (U.rename ρ) (L.rename ρ) (T.rename ρ) (bp.rename ρ) := by
  simp only [decode,DataWrapper.build_rename,DataWrapper.argRen,ite_true, if_true,decoderBody_rename]

theorem decoderBody_subst (L : LogicCode S) (T bp : Expr S) (σ : Nat → Expr S) :
    (R.decoderBody L T bp).subst (Expr.liftSub σ) =
      (R.subst σ).decoderBody (L.subst σ) (T.subst σ) (bp.subst σ) := by
  simp only [decoderBody,Expr.compose_subst,DataWrapper.evalCallback_subst,embedBody_subst,big_subst]
  rfl

theorem decode_subst (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) (σ : Nat → Expr S) :
    (R.decode U L T bp).subst σ =
      (R.subst σ).decode (U.subst σ) (L.subst σ) (T.subst σ) (bp.subst σ) := by
  simp only [decode,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,decoderBody_subst]

end DoubleCode

namespace LogicCode
theorem rename_bottom (L : LogicCode S) (ρ : Nat → Nat) : (L.rename ρ).bottom = L.bottom.rename ρ := rfl
theorem subst_bottom (L : LogicCode S) (σ : Nat → Expr S) : (L.subst σ).bottom = L.bottom.subst σ := rfl
end LogicCode
namespace DoubleCode

section
variable (R : DoubleCode S)
theorem rename_first (ρ : Nat → Nat) : (R.rename ρ).first = R.first.rename ρ := rfl
theorem subst_first (σ : Nat → Expr S) : (R.subst σ).first = R.first.subst σ := rfl
theorem rename_second (ρ : Nat → Nat) : (R.rename ρ).second = R.second.rename ρ := rfl
theorem subst_second (σ : Nat → Expr S) : (R.subst σ).second = R.second.subst σ := rfl
theorem bpBottom_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.bpBottom L T).rename ρ = (R.rename ρ).bpBottom (L.rename ρ) (T.rename ρ) := by
  simp only [bpBottom,DataWrapper.build_rename,big_rename,DataWrapper.argRen,ite_true, if_true,rename_first,LogicCode.rename_bottom,Expr.rename_comp]
  rfl
theorem bpBottom_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.bpBottom L T).subst σ = (R.subst σ).bpBottom (L.subst σ) (T.subst σ) := by
  simp only [bpBottom,DataWrapper.build_subst,big_subst,DataWrapper.argSub,ite_true, if_true,subst_first,LogicCode.subst_bottom,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem paramType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.paramType T).rename ρ = (R.rename ρ).paramType (T.rename ρ) := by
  simp only [paramType,DataWrapper.apply_rename,bpType_rename]; rfl
theorem paramType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.paramType T).subst σ = (R.subst σ).paramType (T.subst σ) := by
  simp only [paramType,DataWrapper.apply_subst,bpType_subst]; rfl
theorem encode_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (ρ : Nat → Nat) :
    (R.encode U L t T p).rename ρ =
      (R.rename ρ).encode (U.rename ρ) (L.rename ρ) t (T.rename ρ) (p.rename ρ) := by
  simp only [encode,DataWrapper.build_rename,DataWrapper.argRen,ite_true, if_true,big_rename,encodeBody_rename]
  rfl
theorem encodeBody_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (σ : Nat → Expr S) :
    (R.encodeBody U L t T p).subst (Expr.liftSub σ) =
      (R.subst σ).encodeBody (U.subst σ) (L.subst σ) t (T.subst σ) (p.subst σ) := by
  simp only [encodeBody,LogicCode.disj_subst,LogicCode.conj_subst,tagBody_subst,
    recoveryBody_subst,DataWrapper.evalCallback_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem encode_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (σ : Nat → Expr S) :
    (R.encode U L t T p).subst σ =
      (R.subst σ).encode (U.subst σ) (L.subst σ) t (T.subst σ) (p.subst σ) := by
  simp only [encode,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,big_subst,encodeBody_subst]
  rfl
theorem dummyBody_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.dummyBody L T).rename (Expr.liftRen ρ) =
      (R.rename ρ).dummyBody (L.rename ρ) (T.rename ρ) := by
  simp only [dummyBody,DataWrapper.contraCallback_rename,bpType_rename,bpBottom_rename]; rfl
theorem dummyBody_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.dummyBody L T).subst (Expr.liftSub σ) =
      (R.subst σ).dummyBody (L.subst σ) (T.subst σ) := by
  simp only [dummyBody,DataWrapper.contraCallback_subst,bpType_subst,bpBottom_subst]; rfl
theorem innerBody_rename (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.innerBody U L T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).innerBody (U.rename ρ) (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [innerBody,LogicCode.cond_rename,dummyBody_rename,queryBody,
    DataWrapper.contraCallback_rename,bpType_rename,encode_rename,LogicCode.rename_comp,rename_second,LogicCode.rename_bottom,Expr.rename_comp]
  rfl
theorem innerBody_subst (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.innerBody U L T p).subst (Expr.liftSub σ) =
      (R.subst σ).innerBody (U.subst σ) (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [innerBody,LogicCode.cond_subst,dummyBody_subst,queryBody,
    DataWrapper.contraCallback_subst,bpType_subst,encode_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,subst_second,LogicCode.subst_bottom,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem innerProbe_rename (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.innerProbe U L T p).rename ρ =
      (R.rename ρ).innerProbe (U.rename ρ) (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [innerProbe,DataWrapper.build_rename,DataWrapper.argRen,ite_true, if_true,paramType_rename,innerBody_rename]
  rfl
theorem innerProbe_subst (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.innerProbe U L T p).subst σ =
      (R.subst σ).innerProbe (U.subst σ) (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [innerProbe,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,paramType_subst,innerBody_subst]
  rfl

theorem query_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) (ρ : Nat → Nat) :
    (R.query U L t T m p).rename ρ =
      (R.rename ρ).query (U.rename ρ) (L.rename ρ) t (T.rename ρ) (m.rename ρ) (p.rename ρ) := by
  simp only [query,DataWrapper.observe_rename,bpType_rename,encode_rename,rename_second,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
theorem query_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) (σ : Nat → Expr S) :
    (R.query U L t T m p).subst σ =
      (R.subst σ).query (U.subst σ) (L.subst σ) t (T.subst σ) (m.subst σ) (p.subst σ) := by
  simp only [query,DataWrapper.observe_subst,bpType_subst,encode_subst,subst_second,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
theorem queryPredBody_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) (ρ : Nat → Nat) :
    (R.queryPredBody U L t T m).rename (Expr.liftRen ρ) =
      (R.rename ρ).queryPredBody (U.rename ρ) (L.rename ρ) t (T.rename ρ) (m.rename ρ) := by
  simp only [queryPredBody,query_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem queryPredBody_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) (σ : Nat → Expr S) :
    (R.queryPredBody U L t T m).subst (Expr.liftSub σ) =
      (R.subst σ).queryPredBody (U.subst σ) (L.subst σ) t (T.subst σ) (m.subst σ) := by
  simp only [queryPredBody,query_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
end

end DoubleCode
namespace ProbeCode

variable (R : ProbeCode S)

theorem funBuild_rename (A Q : Expr S) (ρ : Nat → Nat) :
    (R.funBuild A Q).rename ρ =
      (R.rename ρ).funBuild (A.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [funBuild,Expr.rename,singleType_rename,DataTail.send_rename,rename,DataTail.rename_comp]
  rfl

theorem funBuild_subst (A Q : Expr S) (σ : Nat → Expr S) :
    (R.funBuild A Q).subst σ =
      (R.subst σ).funBuild (A.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [funBuild,Expr.subst,singleType_subst,DataTail.send_subst]
  simp only [subst,DataTail.subst_rename,DataTail.rename_subst]
  rfl

theorem wrappedBuild_rename (A Q : Expr S) (ρ : Nat → Nat) :
    (R.wrappedBuild A Q).rename ρ =
      (R.rename ρ).wrappedBuild (A.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [wrappedBuild,DataWrapper.build_rename,funType_rename,DataWrapper.argRen,
    Bool.false_eq_true,ite_false, if_false,funBuild_rename]
  rfl

theorem wrappedBuild_subst (A Q : Expr S) (σ : Nat → Expr S) :
    (R.wrappedBuild A Q).subst σ =
      (R.subst σ).wrappedBuild (A.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [wrappedBuild,DataWrapper.build_subst,funType_subst,DataWrapper.argSub,
    Bool.false_eq_true,ite_false, if_false,funBuild_subst]
  rfl

end ProbeCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Relational
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
namespace ProbeCode
variable (R : ProbeCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp,PositiveDataWrapper.rename_comp,DataTail.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename,PositiveDataWrapper.subst_rename,DataTail.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst,PositiveDataWrapper.rename_subst,DataTail.rename_subst]
theorem carrier_rename (ρ : Nat → Nat) : R.carrier.rename ρ = (R.rename ρ).carrier := by
  simp only [carrier,body,domain,Expr.rename,DataWrapper.apply_rename,PositiveDataWrapper.apply_rename,
    funType_rename,PositiveDataWrapper.project_rename,DataWrapper.rename_comp,PositiveDataWrapper.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename,DataTail.rename_comp]
  rfl
theorem carrier_subst (σ : Nat → Expr S) : R.carrier.subst σ = (R.subst σ).carrier := by
  simp only [carrier,body,domain,Expr.subst,DataWrapper.apply_subst,PositiveDataWrapper.apply_subst,
    funType_subst,PositiveDataWrapper.project_subst,DataWrapper.subst_rename,
    PositiveDataWrapper.subst_rename,
    subst_rename,rename_subst,Expr.liftSub]
  simp only [subst,DataWrapper.rename_subst,PositiveDataWrapper.rename_subst]
  rfl
theorem readBody_rename (w : Expr S) (ρ : Nat → Nat) :
    (R.readBody w).rename (Expr.liftRen ρ) = (R.rename ρ).readBody (w.rename ρ) := by
  simp only [readBody,DataTail.read_rename,DataTail.rename_comp,Expr.rename,Expr.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename]
  rfl
theorem readBody_subst (w : Expr S) (σ : Nat → Expr S) :
    (R.readBody w).subst (Expr.liftSub σ) = (R.subst σ).readBody (w.subst σ) := by
  simp only [readBody,DataTail.read_subst,DataTail.subst_rename,DataTail.rename_subst,
    Expr.subst,Expr.liftSub,Expr.subst_rename,Expr.rename_subst,subst]
  rfl
theorem observe_rename (A v w : Expr S) (ρ : Nat → Nat) :
    (R.observe A v w).rename ρ = (R.rename ρ).observe (A.rename ρ) (v.rename ρ) (w.rename ρ) := by
  simp only [observe,DataWrapper.observe_rename,funType_rename,specialize,Expr.rename,
    PositiveDataWrapper.inject_rename,readBody_rename,DataWrapper.argRen,Bool.not_false,ite_true, if_true,rename]
theorem observe_subst (A v w : Expr S) (σ : Nat → Expr S) :
    (R.observe A v w).subst σ = (R.subst σ).observe (A.subst σ) (v.subst σ) (w.subst σ) := by
  simp only [observe,DataWrapper.observe_subst,funType_subst,specialize,Expr.subst,
    PositiveDataWrapper.inject_subst,readBody_subst,DataWrapper.argSub,Bool.not_false,ite_true, if_true,subst]
end ProbeCode
namespace DoubleCode
variable (R : DoubleCode S)
theorem decodeMap_rename (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.decodeMap U L T).rename (Expr.liftRen ρ) =
      (R.rename ρ).decodeMap (U.rename ρ) (L.rename ρ) (T.rename ρ) := by
  simp only [decodeMap,decode_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Expr.rename]
  rfl
 theorem markBody_rename (L : LogicCode S) (t : Fin 8) (T c : Expr S) (ρ : Nat → Nat) :
    (R.markBody L t T c).rename (Expr.liftRen ρ) =
      (R.rename ρ).markBody (L.rename ρ) t (T.rename ρ) (c.rename ρ) := by
  simp only [markBody,DataWrapper.contraCallback_rename,big_rename,tagged_rename,rename_first]
 theorem pointBody_rename (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (ρ : Nat → Nat) :
    (R.pointBody U L T c₀ c).rename (Expr.liftRen ρ) =
      (R.rename ρ).pointBody (U.rename ρ) (L.rename ρ) (T.rename ρ) (c₀.rename ρ) (c.rename ρ) := by
  simp only [pointBody,LogicCode.conj_rename,markBody_rename,Expr.compose_rename,
    DataWrapper.contraCallback_rename,decodeMap_rename,LogicCode.rename_comp]
  rfl
 theorem point_rename (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (ρ : Nat → Nat) :
    (R.point U L T c₀ c).rename ρ =
      (R.rename ρ).point (U.rename ρ) (L.rename ρ) (T.rename ρ) (c₀.rename ρ) (c.rename ρ) := by
  simp only [point,DataWrapper.build_rename,bpType_rename,DataWrapper.argRen,ite_true, if_true,
    pointBody_rename,rename_second]
 theorem dummy_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.dummy L T).rename ρ = (R.rename ρ).dummy (L.rename ρ) (T.rename ρ) := by
  simp only [dummy,DataWrapper.build_rename,bpType_rename,DataWrapper.argRen,ite_true, if_true,
    rename_second,Expr.rename_comp,← LogicCode.top_rename]
  rfl
 theorem bundle_rename (L : LogicCode S) (A d m y : Expr S) (ρ : Nat → Nat) :
    (R.bundle L A d m y).rename ρ =
      (R.rename ρ).bundle (L.rename ρ) (A.rename ρ) (d.rename ρ) (m.rename ρ) (y.rename ρ) := by
  simp only [bundle,bundleBody,DataWrapper.build_rename,DataWrapper.apply_rename,DataWrapper.argRen,ite_true, if_true,
    LogicCode.cond_rename,DataWrapper.contraCallback_rename,rename_first,rename_second,LogicCode.rename_comp]
  rfl
theorem decodeMap_subst (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.decodeMap U L T).subst (Expr.liftSub σ) =
      (R.subst σ).decodeMap (U.subst σ) (L.subst σ) (T.subst σ) := by
  simp only [decodeMap,decode_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
 theorem markBody_subst (L : LogicCode S) (t : Fin 8) (T c : Expr S) (σ : Nat → Expr S) :
    (R.markBody L t T c).subst (Expr.liftSub σ) =
      (R.subst σ).markBody (L.subst σ) t (T.subst σ) (c.subst σ) := by
  simp only [markBody,DataWrapper.contraCallback_subst,big_subst,tagged_subst,subst_first]
 theorem pointBody_subst (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (σ : Nat → Expr S) :
    (R.pointBody U L T c₀ c).subst (Expr.liftSub σ) =
      (R.subst σ).pointBody (U.subst σ) (L.subst σ) (T.subst σ) (c₀.subst σ) (c.subst σ) := by
  simp only [pointBody,LogicCode.conj_subst,markBody_subst,Expr.compose_subst,
    DataWrapper.contraCallback_subst,decodeMap_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
 theorem point_subst (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (σ : Nat → Expr S) :
    (R.point U L T c₀ c).subst σ =
      (R.subst σ).point (U.subst σ) (L.subst σ) (T.subst σ) (c₀.subst σ) (c.subst σ) := by
  simp only [point,DataWrapper.build_subst,bpType_subst,DataWrapper.argSub,ite_true, if_true,
    pointBody_subst,subst_second]
 theorem dummy_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.dummy L T).subst σ = (R.subst σ).dummy (L.subst σ) (T.subst σ) := by
  simp only [dummy,DataWrapper.build_subst,bpType_subst,DataWrapper.argSub,ite_true, if_true,
    subst_second,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
 theorem bundle_subst (L : LogicCode S) (A d m y : Expr S) (σ : Nat → Expr S) :
    (R.bundle L A d m y).subst σ =
      (R.subst σ).bundle (L.subst σ) (A.subst σ) (d.subst σ) (m.subst σ) (y.subst σ) := by
  simp only [bundle,bundleBody,DataWrapper.build_subst,DataWrapper.apply_subst,DataWrapper.argSub,ite_true, if_true,
    LogicCode.cond_subst,DataWrapper.contraCallback_subst,subst_first,subst_second,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
end DoubleCode

namespace ChannelCode
variable (R : ChannelCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst]
theorem goodBody_subst (L : LogicCode S) (K : QuantifierCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.goodBody L K T Q).subst (Expr.liftSub σ) =
      (R.subst σ).goodBody (L.subst σ) (K.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [goodBody,LogicCode.conj_subst,roundRespect_subst,subst_rename,rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.subst,Expr.liftSub]
  rfl
end ChannelCode
namespace RelationalCode
variable (R : RelationalCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,ProbeCode.rename_comp,DataWrapper.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,ProbeCode.subst_rename,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,ProbeCode.rename_subst,DataWrapper.rename_subst]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,ProbeCode.instantiate_raise,DataWrapper.instantiate_raise]
theorem channel_rename (ρ : Nat → Nat) : (R.rename ρ).channel = R.channel.rename ρ := rfl
theorem baseType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.baseType A).rename ρ = (R.rename ρ).baseType  (A.rename ρ) :=
  R.probe.initial.apply_rename A ρ
theorem queryBody_rename (L : LogicCode S) (t : Fin 7) (A m : Expr S) (ρ : Nat → Nat) :
    (R.queryBody L t A m).rename (Expr.liftRen ρ) = (R.rename ρ).queryBody (L.rename ρ) t (A.rename ρ) (m.rename ρ) := by
  simp only [queryBody,DoubleCode.queryPredBody_rename,ProbeCode.rawType_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem goodBody_rename (L : LogicCode S) (KY : QuantifierCode S) (A m : Expr S) (ρ : Nat → Nat) :
    (R.goodBody L KY A m).rename (Expr.liftRen ρ) = (R.rename ρ).goodBody (L.rename ρ) (KY.rename ρ) (A.rename ρ) (m.rename ρ) := by
  simp only [goodBody,ChannelCode.goodBody_rename,baseType_rename,queryBody_rename,channel_rename]
theorem pair_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m p a : Expr S) (ρ : Nat → Nat) :
    (R.pair L KY KP A m p a).rename ρ = (R.rename ρ).pair (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (p.rename ρ) (a.rename ρ) := by
  simp only [pair,ChannelCode.pairPred_rename,baseType_rename,goodBody_rename,queryBody_rename,channel_rename]
theorem rawTop_rename (L : LogicCode S) (A : Expr S) (ρ : Nat → Nat) :
    (R.rawTop L A).rename ρ = (R.rename ρ).rawTop (L.rename ρ) (A.rename ρ) := by
  simp only [rawTop,DataWrapper.build_rename,baseType_rename,DataWrapper.argRen,ite_true, if_true,rename,Expr.rename_comp,← LogicCode.top_rename]
  rfl
theorem point_rename (L : LogicCode S) (A y : Expr S) (ρ : Nat → Nat) :
    (R.point L A y).rename ρ = (R.rename ρ).point (L.rename ρ) (A.rename ρ) (y.rename ρ) := by
  simp only [point,DoubleCode.point_rename,ProbeCode.rawType_rename,rawTop_rename,ChannelCode.toRaw_rename,baseType_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem bundle_rename (L : LogicCode S) (A m y : Expr S) (ρ : Nat → Nat) :
    (R.bundle L A m y).rename ρ = (R.rename ρ).bundle (L.rename ρ) (A.rename ρ) (m.rename ρ) (y.rename ρ) := by
  simp only [bundle,DoubleCode.bundle_rename,DoubleCode.dummy_rename,ProbeCode.paramType_rename,ProbeCode.rawType_rename,point_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem diamond_rename (L : LogicCode S) (A m v y : Expr S) (ρ : Nat → Nat) :
    (R.diamond L A m v y).rename ρ = (R.rename ρ).diamond (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [diamond,ProbeCode.observe_rename,bundle_rename,rename]
theorem partBody_rename (L : LogicCode S) (A m v : Expr S) (ρ : Nat → Nat) :
    (R.partBody L A m v).rename (Expr.liftRen ρ) = (R.rename ρ).partBody (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) := by
  simp only [partBody,diamond_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
 theorem part_rename (L : LogicCode S) (A m v : Expr S) (ρ : Nat → Nat) :
    (R.part L A m v).rename ρ = (R.rename ρ).part (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) := by
  simp only [part,ChannelCode.pred_rename,baseType_rename,partBody_rename,channel_rename]
 theorem sb_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m v a : Expr S) (ρ : Nat → Nat) :
    (R.sb L KY KP A m v a).rename ρ = (R.rename ρ).sb (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (v.rename ρ) (a.rename ρ) := by
  simp only [sb,DoubleCode.query_rename,ProbeCode.rawType_rename,pair_rename,part_rename,
    ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
 theorem liftBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (ρ : Nat → Nat) :
    (R.liftBody L KY KP A m a).rename (Expr.liftRen ρ) = (R.rename ρ).liftBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (a.rename ρ) := by
  simp only [liftBody,sb_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen,QuantifierCode.rename,
    ProofWrapper.rename_comp]
  rfl
 theorem lift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (ρ : Nat → Nat) :
    (R.lift L KY KP A m a).rename ρ = (R.rename ρ).lift (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (a.rename ρ) := by
  simp only [lift,DataWrapper.build_rename,ProbeCode.carrier_rename,DataWrapper.argRen,ite_true, if_true,
    liftBody_rename,rename]
theorem channel_subst (σ : Nat → Expr S) : (R.subst σ).channel = R.channel.subst σ := rfl
theorem baseType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.baseType A).subst σ = (R.subst σ).baseType  (A.subst σ) :=
  R.probe.initial.apply_subst A σ
theorem queryBody_subst (L : LogicCode S) (t : Fin 7) (A m : Expr S) (σ : Nat → Expr S) :
    (R.queryBody L t A m).subst (Expr.liftSub σ) = (R.subst σ).queryBody (L.subst σ) t (A.subst σ) (m.subst σ) := by
  simp only [queryBody,DoubleCode.queryPredBody_subst,ProbeCode.rawType_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem goodBody_subst (L : LogicCode S) (KY : QuantifierCode S) (A m : Expr S) (σ : Nat → Expr S) :
    (R.goodBody L KY A m).subst (Expr.liftSub σ) = (R.subst σ).goodBody (L.subst σ) (KY.subst σ) (A.subst σ) (m.subst σ) := by
  simp only [goodBody,ChannelCode.goodBody_subst,baseType_subst,queryBody_subst,channel_subst]
theorem pair_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m p a : Expr S) (σ : Nat → Expr S) :
    (R.pair L KY KP A m p a).subst σ = (R.subst σ).pair (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (p.subst σ) (a.subst σ) := by
  simp only [pair,ChannelCode.pairPred_subst,baseType_subst,goodBody_subst,queryBody_subst,channel_subst]
theorem rawTop_subst (L : LogicCode S) (A : Expr S) (σ : Nat → Expr S) :
    (R.rawTop L A).subst σ = (R.subst σ).rawTop (L.subst σ) (A.subst σ) := by
  simp only [rawTop,DataWrapper.build_subst,baseType_subst,DataWrapper.argSub,ite_true, if_true,subst,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
theorem point_subst (L : LogicCode S) (A y : Expr S) (σ : Nat → Expr S) :
    (R.point L A y).subst σ = (R.subst σ).point (L.subst σ) (A.subst σ) (y.subst σ) := by
  simp only [point,DoubleCode.point_subst,ProbeCode.rawType_subst,rawTop_subst,ChannelCode.toRaw_subst,baseType_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem bundle_subst (L : LogicCode S) (A m y : Expr S) (σ : Nat → Expr S) :
    (R.bundle L A m y).subst σ = (R.subst σ).bundle (L.subst σ) (A.subst σ) (m.subst σ) (y.subst σ) := by
  simp only [bundle,DoubleCode.bundle_subst,DoubleCode.dummy_subst,ProbeCode.paramType_subst,ProbeCode.rawType_subst,point_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem diamond_subst (L : LogicCode S) (A m v y : Expr S) (σ : Nat → Expr S) :
    (R.diamond L A m v y).subst σ = (R.subst σ).diamond (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [diamond,ProbeCode.observe_subst,bundle_subst,subst]
theorem partBody_subst (L : LogicCode S) (A m v : Expr S) (σ : Nat → Expr S) :
    (R.partBody L A m v).subst (Expr.liftSub σ) = (R.subst σ).partBody (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) := by
  simp only [partBody,diamond_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
 theorem part_subst (L : LogicCode S) (A m v : Expr S) (σ : Nat → Expr S) :
    (R.part L A m v).subst σ = (R.subst σ).part (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) := by
  simp only [part,ChannelCode.pred_subst,baseType_subst,partBody_subst,channel_subst]
 theorem sb_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m v a : Expr S) (σ : Nat → Expr S) :
    (R.sb L KY KP A m v a).subst σ = (R.subst σ).sb (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (v.subst σ) (a.subst σ) := by
  simp only [sb,DoubleCode.query_subst,ProbeCode.rawType_subst,pair_subst,part_subst,
    ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
 theorem liftBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (σ : Nat → Expr S) :
    (R.liftBody L KY KP A m a).subst (Expr.liftSub σ) = (R.subst σ).liftBody (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (a.subst σ) := by
  simp only [liftBody,sb_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst]
  rfl
 theorem lift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (σ : Nat → Expr S) :
    (R.lift L KY KP A m a).subst σ = (R.subst σ).lift (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (a.subst σ) := by
  simp only [lift,DataWrapper.build_subst,ProbeCode.carrier_subst,DataWrapper.argSub,ite_true, if_true,
    liftBody_subst,subst]
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace RelationalCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h)
include H
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (R.rename e.names).Formed (L.rename e) I J k p n g j h :=
  ⟨H.probe.rename e,H.channel.rename e⟩
end

end RelationalCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)
theorem accessBody_rename (L : LogicCode S) (A guard w fi : Expr S) (ρ : Nat → Nat) :
    (R.accessBody L A guard w fi).rename (Expr.liftRen ρ) =
      (R.rename ρ).accessBody (L.rename ρ) (A.rename ρ) (guard.rename (Expr.liftRen ρ)) (w.rename ρ) (fi.rename (Expr.liftRen ρ)) := by
  simp only [accessBody,LogicCode.cond_rename,Expr.compose_rename,DataWrapper.evalCallback_rename,
    DataWrapper.apply_rename,rename_first,rename_second,LogicCode.rename_comp,Expr.rename_comp,← LogicCode.top_rename]
  rfl
theorem accessBody_subst (L : LogicCode S) (A guard w fi : Expr S) (σ : Nat → Expr S) :
    (R.accessBody L A guard w fi).subst (Expr.liftSub σ) =
      (R.subst σ).accessBody (L.subst σ) (A.subst σ) (guard.subst (Expr.liftSub σ)) (w.subst σ) (fi.subst (Expr.liftSub σ)) := by
  simp only [accessBody,LogicCode.cond_subst,Expr.compose_subst,DataWrapper.evalCallback_subst,
    DataWrapper.apply_subst,subst_first,subst_second,LogicCode.subst_rename,LogicCode.rename_subst,
    Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
theorem access_rename (L : LogicCode S) (A guard w fi : Expr S) (ρ : Nat → Nat) :
    (R.access L A guard w fi).rename ρ = (R.rename ρ).access (L.rename ρ) (A.rename ρ)
      (guard.rename (Expr.liftRen ρ)) (w.rename ρ) (fi.rename (Expr.liftRen ρ)) := by
  simp only [access,accessProbe,DataWrapper.observe_rename,DataWrapper.apply_rename,
    DataWrapper.build_rename,accessBody_rename,rename_first,rename_second,DataWrapper.argRen,
    Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
theorem access_subst (L : LogicCode S) (A guard w fi : Expr S) (σ : Nat → Expr S) :
    (R.access L A guard w fi).subst σ = (R.subst σ).access (L.subst σ) (A.subst σ)
      (guard.subst (Expr.liftSub σ)) (w.subst σ) (fi.subst (Expr.liftSub σ)) := by
  simp only [access,accessProbe,DataWrapper.observe_subst,DataWrapper.apply_subst,
    DataWrapper.build_subst,accessBody_subst,subst_first,subst_second,DataWrapper.argSub,
    Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
theorem innerMap_rename (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.innerMap U L T).rename (Expr.liftRen ρ) = (R.rename ρ).innerMap (U.rename ρ) (L.rename ρ) (T.rename ρ) := by
  simp only [innerMap,innerProbe_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem innerMap_subst (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.innerMap U L T).subst (Expr.liftSub σ) = (R.subst σ).innerMap (U.subst σ) (L.subst σ) (T.subst σ) := by
  simp only [innerMap,innerProbe_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem recoverAccess_rename (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) (ρ : Nat → Nat) :
    (R.recoverAccess U L T w pMap).rename ρ = (R.rename ρ).recoverAccess (U.rename ρ) (L.rename ρ)
      (T.rename ρ) (w.rename ρ) (pMap.rename (Expr.liftRen ρ)) := by
  simp only [recoverAccess,access_rename,paramType_rename,dummyBody_rename,accessMap,Expr.compose_rename,innerMap_rename]
theorem recoverAccess_subst (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) (σ : Nat → Expr S) :
    (R.recoverAccess U L T w pMap).subst σ = (R.subst σ).recoverAccess (U.subst σ) (L.subst σ)
      (T.subst σ) (w.subst σ) (pMap.subst (Expr.liftSub σ)) := by
  simp only [recoverAccess,access_subst,paramType_subst,dummyBody_subst,accessMap,Expr.compose_subst,innerMap_subst]
end DoubleCode
end

section
universe u
variable {S : Type u}
namespace RelationalCode
variable (R : RelationalCode S)
theorem liftEvalBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (ρ : Nat → Nat) :
    (R.liftEvalBody L KY KP A m i).rename (Expr.liftRen ρ) = (R.rename ρ).liftEvalBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (i.rename ρ) := by
  simp only [liftEvalBody,ChannelCode.eval_rename,lift_rename,channel_rename,ProbeCode.carrier_rename,ChannelCode.rename_comp,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  simp only [rename,ProbeCode.rename_comp]
  rfl
theorem predLift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (ρ : Nat → Nat) :
    (R.predLift L KY KP A m i).rename ρ = (R.rename ρ).predLift (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (i.rename ρ) := by
  simp only [predLift,ChannelCode.pred_rename,baseType_rename,liftEvalBody_rename,channel_rename]
theorem predLiftMap_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (ρ : Nat → Nat) :
    (R.predLiftMap L KY KP A i).rename (Expr.liftRen ρ) = (R.rename ρ).predLiftMap (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) := by
  simp only [predLiftMap,predLift_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem recoverLift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) (ρ : Nat → Nat) :
    (R.recoverLift L KY KP A i w).rename ρ = (R.rename ρ).recoverLift (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) (w.rename ρ) := by
  simp only [recoverLift,DoubleCode.recoverAccess_rename,ProbeCode.rawType_rename,predLiftMap_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem recoverLiftBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (ρ : Nat → Nat) :
    (R.recoverLiftBody L KY KP A i).rename (Expr.liftRen ρ) = (R.rename ρ).recoverLiftBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) := by
  simp only [recoverLiftBody,recoverLift_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem liftEvalBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (σ : Nat → Expr S) :
    (R.liftEvalBody L KY KP A m i).subst (Expr.liftSub σ) = (R.subst σ).liftEvalBody (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (i.subst σ) := by
  simp only [liftEvalBody,ChannelCode.eval_subst,lift_subst,channel_subst,ProbeCode.carrier_subst,ChannelCode.subst_rename,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub,ChannelCode.rename_subst]
  simp only [subst,ProbeCode.carrier_rename,ProbeCode.rename_subst]
  rfl
theorem predLift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (σ : Nat → Expr S) :
    (R.predLift L KY KP A m i).subst σ = (R.subst σ).predLift (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (i.subst σ) := by
  simp only [predLift,ChannelCode.pred_subst,baseType_subst,liftEvalBody_subst,channel_subst]
theorem predLiftMap_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (σ : Nat → Expr S) :
    (R.predLiftMap L KY KP A i).subst (Expr.liftSub σ) = (R.subst σ).predLiftMap (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) := by
  simp only [predLiftMap,predLift_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem recoverLift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) (σ : Nat → Expr S) :
    (R.recoverLift L KY KP A i w).subst σ = (R.subst σ).recoverLift (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) (w.subst σ) := by
  simp only [recoverLift,DoubleCode.recoverAccess_subst,ProbeCode.rawType_subst,predLiftMap_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem recoverLiftBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (σ : Nat → Expr S) :
    (R.recoverLiftBody L KY KP A i).subst (Expr.liftSub σ) = (R.subst σ).recoverLiftBody (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) := by
  simp only [recoverLiftBody,recoverLift_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
end RelationalCode

namespace ProbeCode
variable (R : ProbeCode S)
theorem uniform_rename (Q : Expr S) (ρ : Nat → Nat) :
    (R.uniform Q).rename ρ = (R.rename ρ).uniform (Q.rename (Expr.liftRen (Expr.liftRen ρ))) := by
  simp only [uniform,Expr.rename,domain,PositiveDataWrapper.apply_rename,wrappedBuild_rename,
    PositiveDataWrapper.project_rename,PositiveDataWrapper.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename]
  simp only [DataWrapper.rename_comp,DataTail.rename_comp]
  rfl
theorem uniform_subst (Q : Expr S) (σ : Nat → Expr S) :
    (R.uniform Q).subst σ = (R.subst σ).uniform (Q.subst (Expr.liftSub (Expr.liftSub σ))) := by
  simp only [uniform,Expr.subst,domain,PositiveDataWrapper.apply_subst,wrappedBuild_subst,
    PositiveDataWrapper.project_subst,subst_rename,rename_subst,PositiveDataWrapper.subst_rename,
    Expr.liftSub]
  simp only [subst,PositiveDataWrapper.rename_subst]
  rfl
end ProbeCode
namespace RelationalCode
variable (R : RelationalCode S)
theorem probeFor_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.probeFor L KY KP i).rename ρ =
      (R.rename ρ).probeFor (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [probeFor,ProbeCode.uniform_rename,recoverLiftBody_rename,
    LogicCode.rename_comp,QuantifierCode.rename_comp,PositiveDataWrapper.project_rename,
    PositiveDataWrapper.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen,rename,ProbeCode.rename]
  simp only [DataWrapper.rename_comp,DataTail.rename_comp]
  rfl
theorem probeFor_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.probeFor L KY KP i).subst σ =
      (R.subst σ).probeFor (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [probeFor,ProbeCode.uniform_subst,recoverLiftBody_subst,subst_rename,rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,PositiveDataWrapper.project_subst,
    PositiveDataWrapper.subst_rename,Expr.subst_rename,
    Expr.rename_subst,Expr.subst,Expr.liftSub]
  simp only [subst,ProbeCode.subst,PositiveDataWrapper.rename_subst]
  rfl
theorem le_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.le L KY KP i x).rename ρ = (R.rename ρ).le (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [le,DataWrapper.observe_rename,ProbeCode.carrier_rename,probeFor_rename,DataWrapper.argRen,rename]
  rfl
theorem le_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.le L KY KP i x).subst σ = (R.subst σ).le (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [le,DataWrapper.observe_subst,ProbeCode.carrier_subst,probeFor_subst,DataWrapper.argSub,subst]
  rfl
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}

namespace RelationalCode
variable (R : RelationalCode S)

theorem leBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.leBody L KY KP x).rename (Expr.liftRen ρ) =
      (R.rename ρ).leBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [leBody,le_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem leBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.leBody L KY KP x).subst (Expr.liftSub σ) =
      (R.subst σ).leBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [leBody,le_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem xCompareBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (ρ : Nat → Nat) :
    (R.xCompareBody L KY KP x y).rename (Expr.liftRen ρ) =
      (R.rename ρ).xCompareBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [xCompareBody,LogicCode.iff_rename,leBody_rename,LogicCode.rename_comp]
  rfl
theorem xCompareBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (σ : Nat → Expr S) :
    (R.xCompareBody L KY KP x y).subst (Expr.liftSub σ) =
      (R.subst σ).xCompareBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [xCompareBody,LogicCode.iff_subst,leBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem xCompare_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (ρ : Nat → Nat) :
    (R.xCompare L KY KP x y).rename ρ =
      (R.rename ρ).xCompare (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [xCompare,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,
    channel_rename,xCompareBody_rename]
  rfl
theorem xCompare_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (σ : Nat → Expr S) :
    (R.xCompare L KY KP x y).subst σ =
      (R.subst σ).xCompare (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [xCompare,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,
    channel_subst,xCompareBody_subst]
  rfl

end RelationalCode
end

section
universe u
namespace RelationalCode
variable {S : Type u} (R : RelationalCode S)

theorem extStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) (ρ : Nat → Nat) :
    (R.extStep L KY KP i x y).rename ρ =
      (R.rename ρ).extStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [extStep,LogicCode.imp_rename,LogicCode.iff_rename,xCompare_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,channel_rename]
  try rfl

theorem extStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) (σ : Nat → Expr S) :
    (R.extStep L KY KP i x y).subst σ =
      (R.subst σ).extStep (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [extStep,LogicCode.imp_subst,LogicCode.iff_subst,xCompare_subst,ChannelCode.eval_subst,ProbeCode.carrier_subst,channel_subst]
  try rfl

theorem extAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.extAtBody L KY KP i x).rename (Expr.liftRen ρ) =
      (R.rename ρ).extAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [extAtBody,extStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem extAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.extAtBody L KY KP i x).subst (Expr.liftSub σ) =
      (R.subst σ).extAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [extAtBody,extStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem extAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.extAt L KY KP i x).rename ρ =
      (R.rename ρ).extAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [extAt,QuantifierCode.all_rename,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,extAtBody_rename]
  try rfl

theorem extAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.extAt L KY KP i x).subst σ =
      (R.subst σ).extAt (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [extAt,QuantifierCode.all_subst,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,channel_subst,extAtBody_subst]
  try rfl

theorem extBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.extBody L KY KP i).rename (Expr.liftRen ρ) =
      (R.rename ρ).extBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [extBody,extAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem extBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.extBody L KY KP i).subst (Expr.liftSub σ) =
      (R.subst σ).extBody (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [extBody,extAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem extensional_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.extensional L KY KP i).rename ρ =
      (R.rename ρ).extensional (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [extensional,QuantifierCode.all_rename,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,extBody_rename]
  try rfl

theorem extensional_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.extensional L KY KP i).subst σ =
      (R.subst σ).extensional (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [extensional,QuantifierCode.all_subst,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,channel_subst,extBody_subst]
  try rfl

theorem validStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) (ρ : Nat → Nat) :
    (R.validStep L KY KP x i i').rename ρ =
      (R.rename ρ).validStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) (i'.rename ρ) := by
  simp only [validStep,LogicCode.imp_rename,LogicCode.iff_rename,ChannelCode.predCompare_rename,ProbeCode.carrier_rename,channel_rename,le_rename]
  try rfl

theorem validStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) (σ : Nat → Expr S) :
    (R.validStep L KY KP x i i').subst σ =
      (R.subst σ).validStep (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) (i'.subst σ) := by
  simp only [validStep,LogicCode.imp_subst,LogicCode.iff_subst,ChannelCode.predCompare_subst,ProbeCode.carrier_subst,channel_subst,le_subst]
  try rfl

theorem validAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (ρ : Nat → Nat) :
    (R.validAtBody L KY KP x i).rename (Expr.liftRen ρ) =
      (R.rename ρ).validAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) := by
  simp only [validAtBody,validStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem validAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (σ : Nat → Expr S) :
    (R.validAtBody L KY KP x i).subst (Expr.liftSub σ) =
      (R.subst σ).validAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) := by
  simp only [validAtBody,validStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem validAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (ρ : Nat → Nat) :
    (R.validAt L KY KP x i).rename ρ =
      (R.rename ρ).validAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) := by
  simp only [validAt,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,validAtBody_rename]
  try rfl

theorem validAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (σ : Nat → Expr S) :
    (R.validAt L KY KP x i).subst σ =
      (R.subst σ).validAt (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) := by
  simp only [validAt,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,channel_subst,validAtBody_subst]
  try rfl

theorem validBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.validBody L KY KP x).rename (Expr.liftRen ρ) =
      (R.rename ρ).validBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [validBody,validAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem validBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.validBody L KY KP x).subst (Expr.liftSub σ) =
      (R.subst σ).validBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [validBody,validAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem valid_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.valid L KY KP x).rename ρ =
      (R.rename ρ).valid (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [valid,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,validBody_rename]
  try rfl

theorem valid_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.valid L KY KP x).subst σ =
      (R.subst σ).valid (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [valid,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,channel_subst,validBody_subst]
  try rfl
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}

namespace RelationalCode
variable (R : RelationalCode S)
theorem p_type_rename (ρ : Nat → Nat) :
    (R.channel.predicateType R.probe.carrier).rename ρ =
      (R.rename ρ).channel.predicateType (R.rename ρ).probe.carrier := by
  simp only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename]
  rfl
end RelationalCode

end

universe u
variable {S : Type u}
namespace ThreeCopyCode
variable (R : ThreeCopyCode S)
theorem firstType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.firstType T).rename ρ = (R.rename ρ).firstType (T.rename ρ) := by
  simp only [firstType,DataWrapper.apply_rename,rename]
theorem firstType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.firstType T).subst σ = (R.subst σ).firstType (T.subst σ) := by
  simp only [firstType,DataWrapper.apply_subst,subst]
theorem middleType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.middleType T).rename ρ = (R.rename ρ).middleType (T.rename ρ) := by
  simp only [middleType,DoubleCode.carrier_rename,firstType_rename,rename]
theorem middleType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.middleType T).subst σ = (R.subst σ).middleType (T.subst σ) := by
  simp only [middleType,DoubleCode.carrier_subst,firstType_subst,subst]
theorem carrier_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.carrier T).rename ρ = (R.rename ρ).carrier (T.rename ρ) := by
  simp only [carrier,DoubleCode.carrier_rename,middleType_rename,rename]
theorem carrier_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.carrier T).subst σ = (R.subst σ).carrier (T.subst σ) := by
  simp only [carrier,DoubleCode.carrier_subst,middleType_subst,subst]
theorem bitInner_rename (L : LogicCode S) (T y : Expr S) (ρ : Nat → Nat) :
    (R.bitInner L T y).rename ρ = (R.rename ρ).bitInner (L.rename ρ) (T.rename ρ) (y.rename ρ) := by
  simp only [bitInner,DoubleCode.rec_rename,DoubleCode.bitBody_rename,middleType_rename,firstType_rename,rename]
theorem bitInner_subst (L : LogicCode S) (T y : Expr S) (σ : Nat → Expr S) :
    (R.bitInner L T y).subst σ = (R.subst σ).bitInner (L.subst σ) (T.subst σ) (y.subst σ) := by
  simp only [bitInner,DoubleCode.rec_subst,DoubleCode.bitBody_subst,middleType_subst,firstType_subst,subst]
theorem bitOuter_rename (L : LogicCode S) (T y : Expr S) (ρ : Nat → Nat) :
    (R.bitOuter L T y).rename ρ = (R.rename ρ).bitOuter (L.rename ρ) (T.rename ρ) (y.rename ρ) := by
  simp only [bitOuter,DoubleCode.bit_rename,middleType_rename,rename]
theorem bitOuter_subst (L : LogicCode S) (T y : Expr S) (σ : Nat → Expr S) :
    (R.bitOuter L T y).subst σ = (R.subst σ).bitOuter (L.subst σ) (T.subst σ) (y.subst σ) := by
  simp only [bitOuter,DoubleCode.bit_subst,middleType_subst,subst]
theorem observe_rename (L : LogicCode S) (T y a : Expr S) (ρ : Nat → Nat) :
    (R.observe L T y a).rename ρ = (R.rename ρ).observe (L.rename ρ) (T.rename ρ) (y.rename ρ) (a.rename ρ) := by
  simp only [observe,DoubleCode.rec_rename,DoubleCode.recBody_rename,DataWrapper.contraCallback_rename,middleType_rename,firstType_rename,rename]
theorem observe_subst (L : LogicCode S) (T y a : Expr S) (σ : Nat → Expr S) :
    (R.observe L T y a).subst σ = (R.subst σ).observe (L.subst σ) (T.subst σ) (y.subst σ) (a.subst σ) := by
  simp only [observe,DoubleCode.rec_subst,DoubleCode.recBody_subst,DataWrapper.contraCallback_subst,middleType_subst,firstType_subst,subst]
theorem tagged_rename (L : LogicCode S) (t : Fin 3) (T x : Expr S) (ρ : Nat → Nat) :
    (R.tagged L t T x).rename ρ = (R.rename ρ).tagged (L.rename ρ) t (T.rename ρ) (x.rename ρ) := by
  simp only [tagged,DoubleCode.emb_rename,DataWrapper.reencode_rename,middleType_rename,firstType_rename,rename]
theorem tagged_subst (L : LogicCode S) (t : Fin 3) (T x : Expr S) (σ : Nat → Expr S) :
    (R.tagged L t T x).subst σ = (R.subst σ).tagged (L.subst σ) t (T.subst σ) (x.subst σ) := by
  simp only [tagged,DoubleCode.emb_subst,DataWrapper.reencode_subst,middleType_subst,firstType_subst,subst]
end ThreeCopyCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Specialization
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
namespace ObservationCode
variable (O : ObservationCode S)

theorem rename_comp (ρ τ : Nat → Nat) : (O.rename τ).rename ρ = O.rename (ρ ∘ τ) := by
  cases O; simp only [rename,RelationalCode.rename_comp,DoubleCode.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (O.rename ρ).subst σ = O.subst (σ ∘ ρ) := by
  cases O; simp only [rename,subst,RelationalCode.subst_rename,DoubleCode.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (O.subst σ).rename ρ = O.subst (fun i => (σ i).rename ρ) := by
  cases O; simp only [rename,subst,RelationalCode.rename_subst,DoubleCode.rename_subst]
theorem instantiate_raise (a : Expr S) : (O.rename Nat.succ).subst (Expr.single a) = O := by
  cases O; simp only [rename,subst,RelationalCode.instantiate_raise,DoubleCode.instantiate_raise]
theorem copies_rename (ρ : Nat → Nat) : O.copies.rename ρ = (O.rename ρ).copies := rfl
theorem copies_subst (σ : Nat → Expr S) : O.copies.subst σ = (O.subst σ).copies := rfl
theorem carrier_rename (ρ : Nat → Nat) :
    (O.carrier ).rename ρ = (O.rename ρ).carrier  := by
  simp only [carrier,ThreeCopyCode.carrier_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem carrier_subst (σ : Nat → Expr S) :
    (O.carrier ).subst σ = (O.subst σ).carrier  := by
  simp only [carrier,ThreeCopyCode.carrier_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem tagged_rename (L : LogicCode S) (t : Fin 3) (x : Expr S) (ρ : Nat → Nat) :
    (O.tagged L t x).rename ρ = (O.rename ρ).tagged (L.rename ρ) t (x.rename ρ) := by
  simp only [tagged,ThreeCopyCode.tagged_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem tagged_subst (L : LogicCode S) (t : Fin 3) (x : Expr S) (σ : Nat → Expr S) :
    (O.tagged L t x).subst σ = (O.subst σ).tagged (L.subst σ) t (x.subst σ) := by
  simp only [tagged,ThreeCopyCode.tagged_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem bitInner_rename (L : LogicCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.bitInner L y).rename ρ = (O.rename ρ).bitInner (L.rename ρ) (y.rename ρ) := by
  simp only [bitInner,ThreeCopyCode.bitInner_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem bitInner_subst (L : LogicCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.bitInner L y).subst σ = (O.subst σ).bitInner (L.subst σ) (y.subst σ) := by
  simp only [bitInner,ThreeCopyCode.bitInner_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem bitOuter_rename (L : LogicCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.bitOuter L y).rename ρ = (O.rename ρ).bitOuter (L.rename ρ) (y.rename ρ) := by
  simp only [bitOuter,ThreeCopyCode.bitOuter_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem bitOuter_subst (L : LogicCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.bitOuter L y).subst σ = (O.subst σ).bitOuter (L.subst σ) (y.subst σ) := by
  simp only [bitOuter,ThreeCopyCode.bitOuter_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem observe_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) (ρ : Nat → Nat) :
    (O.observe L KY KP i y).rename ρ = (O.rename ρ).observe (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (y.rename ρ) := by
  simp only [observe,ThreeCopyCode.observe_rename,copies_rename,ProbeCode.carrier_rename,RelationalCode.probeFor_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem observe_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) (σ : Nat → Expr S) :
    (O.observe L KY KP i y).subst σ = (O.subst σ).observe (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (y.subst σ) := by
  simp only [observe,ThreeCopyCode.observe_subst,copies_subst,ProbeCode.carrier_subst,RelationalCode.probeFor_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem observeBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.observeBody L KY KP y).rename (Expr.liftRen ρ) = (O.rename ρ).observeBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) := by
  simp only [observeBody,observe_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem observeBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.observeBody L KY KP y).subst (Expr.liftSub σ) = (O.subst σ).observeBody (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) := by
  simp only [observeBody,observe_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem compareBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.compareBody L KY KP y z).rename (Expr.liftRen ρ) = (O.rename ρ).compareBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compareBody,LogicCode.iff_rename,observeBody_rename,LogicCode.rename_comp]
  try rfl
theorem compareBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.compareBody L KY KP y z).subst (Expr.liftSub σ) = (O.subst σ).compareBody (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compareBody,LogicCode.iff_subst,observeBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  try rfl
theorem compare_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.compare L KY KP y z).rename ρ = (O.rename ρ).compare (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compare,QuantifierCode.all_rename,RelationalCode.p_type_rename,compareBody_rename]
  try rfl
theorem compare_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.compare L KY KP y z).subst σ = (O.subst σ).compare (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compare,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst,compareBody_subst]
  try rfl
theorem ae_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.ae L KY KP y z).rename ρ = (O.rename ρ).ae (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [ae,LogicCode.conj_rename,LogicCode.iff_rename,bitInner_rename,bitOuter_rename,compare_rename]
  try rfl
theorem ae_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.ae L KY KP y z).subst σ = (O.subst σ).ae (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [ae,LogicCode.conj_subst,LogicCode.iff_subst,bitInner_subst,bitOuter_subst,compare_subst]
  try rfl
end ObservationCode
end

section
universe u
namespace SpecializedCode
variable {S : Type u} (B : SpecializedCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (B.rename ρ).rename τ = B.rename (τ ∘ ρ) := by
  simp only [rename,ObservationCode.rename_comp,Expr.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) : (B.rename ρ).subst σ = B.subst (σ ∘ ρ) := by
  simp only [rename,subst,ObservationCode.subst_rename,Expr.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) : (B.subst σ).rename ρ = B.subst (fun n => (σ n).rename ρ) := by
  simp only [rename,subst,ObservationCode.rename_subst,Expr.rename_subst]
theorem instantiate_raise (a : Expr S) : (B.rename Nat.succ).subst (Expr.single a) = B := by
  simp only [rename,subst,ObservationCode.instantiate_raise,Expr.subst_lift_single]
theorem baseType_rename (ρ : Nat → Nat) : (B.baseType ).rename ρ = (B.rename ρ).baseType  := by
  simp only [baseType,RelationalCode.baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem baseType_subst (σ : Nat → Expr S) : (B.baseType ).subst σ = (B.subst σ).baseType  := by
  simp only [baseType,RelationalCode.baseType_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem xType_rename (ρ : Nat → Nat) : (B.xType ).rename ρ = (B.rename ρ).xType  := by
  simp only [xType,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem xType_subst (σ : Nat → Expr S) : (B.xType ).subst σ = (B.subst σ).xType  := by
  simp only [xType,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem yType_rename (ρ : Nat → Nat) : (B.yType ).rename ρ = (B.rename ρ).yType  := by
  simp only [yType,ObservationCode.carrier_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem yType_subst (σ : Nat → Expr S) : (B.yType ).subst σ = (B.subst σ).yType  := by
  simp only [yType,ObservationCode.carrier_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem predType_rename (ρ : Nat → Nat) : (B.predType ).rename ρ = (B.rename ρ).predType  := by
  simp only [predType,ChannelCode.predicateType_rename,baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem ev_rename (v y : Expr S) (ρ : Nat → Nat) : (B.ev v y).rename ρ = (B.rename ρ).ev (v.rename ρ) (y.rename ρ) := by
  simp only [ev,ChannelCode.eval_rename,baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem ev_subst (v y : Expr S) (σ : Nat → Expr S) : (B.ev v y).subst σ = (B.subst σ).ev (v.subst σ) (y.subst σ) := by
  simp only [ev,ChannelCode.eval_subst,baseType_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem gStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (ρ : Nat → Nat) :
    (B.gStep L KY KP v y z).rename ρ = (B.rename ρ).gStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [gStep,LogicCode.imp_rename,LogicCode.iff_rename,ObservationCode.ae_rename,ev_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem gStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (σ : Nat → Expr S) :
    (B.gStep L KY KP v y z).subst σ = (B.subst σ).gStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [gStep,LogicCode.imp_subst,LogicCode.iff_subst,ObservationCode.ae_subst,ev_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem gAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.gAtBody L KY KP v y).rename (Expr.liftRen ρ) = (B.rename ρ).gAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [gAtBody,gStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem gAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.gAtBody L KY KP v y).subst (Expr.liftSub σ) = (B.subst σ).gAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [gAtBody,gStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem gAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.gAt L KY KP v y).rename ρ = (B.rename ρ).gAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [gAt,QuantifierCode.all_rename,yType_rename,gAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem gAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.gAt L KY KP v y).subst σ = (B.subst σ).gAt (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [gAt,QuantifierCode.all_subst,yType_subst,gAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem gBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.gBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).gBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [gBody,gAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem gBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.gBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).gBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [gBody,gAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyG_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyG L KY KP v).rename ρ = (B.rename ρ).propertyG (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [propertyG,QuantifierCode.all_rename,yType_rename,gBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyG_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyG L KY KP v).subst σ = (B.subst σ).propertyG (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [propertyG,QuantifierCode.all_subst,yType_subst,gBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (ρ : Nat → Nat) :
    (B.cStep L KY KP t v x w).rename ρ = (B.rename ρ).cStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) (w.rename ρ) := by
  simp only [cStep,LogicCode.iff_rename,ev_rename,ObservationCode.ae_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem cStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (σ : Nat → Expr S) :
    (B.cStep L KY KP t v x w).subst σ = (B.subst σ).cStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) (w.subst σ) := by
  simp only [cStep,LogicCode.iff_subst,ev_subst,ObservationCode.ae_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.cAtBody L KY KP t v x).rename (Expr.liftRen ρ) = (B.rename ρ).cAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [cAtBody,cStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem cAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.cAtBody L KY KP t v x).subst (Expr.liftSub σ) = (B.subst σ).cAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [cAtBody,cStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem cAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.cAt L KY KP t v x).rename ρ = (B.rename ρ).cAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [cAt,QuantifierCode.all_rename,yType_rename,cAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem cAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.cAt L KY KP t v x).subst σ = (B.subst σ).cAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [cAt,QuantifierCode.all_subst,yType_subst,cAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.cBody L KY KP t v).rename (Expr.liftRen ρ) = (B.rename ρ).cBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [cBody,cAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem cBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.cBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).cBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [cBody,cAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyC_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyC L KY KP t v).rename ρ = (B.rename ρ).propertyC (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [propertyC,LogicCode.ex_rename,xType_rename,cBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyC_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyC L KY KP t v).subst σ = (B.subst σ).propertyC (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [propertyC,LogicCode.ex_subst,xType_subst,cBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (ρ : Nat → Nat) :
    (B.eStep L KY KP t v x w).rename ρ = (B.rename ρ).eStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) (w.rename ρ) := by
  simp only [eStep,LogicCode.iff_rename,LogicCode.disj_rename,ev_rename,ObservationCode.ae_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem eStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (σ : Nat → Expr S) :
    (B.eStep L KY KP t v x w).subst σ = (B.subst σ).eStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) (w.subst σ) := by
  simp only [eStep,LogicCode.iff_subst,LogicCode.disj_subst,ev_subst,ObservationCode.ae_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.eAtBody L KY KP t v x).rename (Expr.liftRen ρ) = (B.rename ρ).eAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [eAtBody,eStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem eAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.eAtBody L KY KP t v x).subst (Expr.liftSub σ) = (B.subst σ).eAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [eAtBody,eStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem eAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.eAt L KY KP t v x).rename ρ = (B.rename ρ).eAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [eAt,QuantifierCode.all_rename,yType_rename,eAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem eAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.eAt L KY KP t v x).subst σ = (B.subst σ).eAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [eAt,QuantifierCode.all_subst,yType_subst,eAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.eBody L KY KP t v).rename (Expr.liftRen ρ) = (B.rename ρ).eBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [eBody,eAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem eBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.eBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).eBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [eBody,eAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyE_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyE L KY KP t v).rename ρ = (B.rename ρ).propertyE (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [propertyE,LogicCode.ex_rename,xType_rename,eBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyE_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyE L KY KP t v).subst σ = (B.subst σ).propertyE (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [propertyE,LogicCode.ex_subst,xType_subst,eBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rPredStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.rPredStep L KY KP v x).rename ρ = (B.rename ρ).rPredStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [rPredStep,ev_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rPredStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.rPredStep L KY KP v x).subst σ = (B.subst σ).rPredStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [rPredStep,ev_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rPredBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rPredBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).rPredBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rPredBody,rPredStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem rPredBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rPredBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).rPredBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rPredBody,rPredStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem rPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rPred L KY KP v).rename ρ = (B.rename ρ).rPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rPred,ChannelCode.pred_rename,ProbeCode.carrier_rename,rPredBody_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem rPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rPred L KY KP v).subst σ = (B.subst σ).rPred (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rPred,ChannelCode.pred_subst,ProbeCode.carrier_subst,rPredBody_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem rStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.rStep L KY KP v x).rename ρ = (B.rename ρ).rStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [rStep,LogicCode.imp_rename,RelationalCode.valid_rename,ev_rename,ObservationCode.tagged_rename,RelationalCode.le_rename,rPred_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.rStep L KY KP v x).subst σ = (B.subst σ).rStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [rStep,LogicCode.imp_subst,RelationalCode.valid_subst,ev_subst,ObservationCode.tagged_subst,RelationalCode.le_subst,rPred_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).rBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rBody,rStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem rBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).rBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rBody,rStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem rAll_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rAll L KY KP v).rename ρ = (B.rename ρ).rAll (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rAll,QuantifierCode.all_rename,xType_rename,rBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rAll_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rAll L KY KP v).subst σ = (B.subst σ).rAll (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rAll,QuantifierCode.all_subst,xType_subst,rBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem propertyR_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyR L KY KP v).rename ρ = (B.rename ρ).propertyR (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [propertyR,LogicCode.imp_rename,RelationalCode.extensional_rename,rPred_rename,rAll_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyR_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyR L KY KP v).subst σ = (B.subst σ).propertyR (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [propertyR,LogicCode.imp_subst,RelationalCode.extensional_subst,rPred_subst,rAll_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
end SpecializedCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace ObservationCode
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (O : ObservationCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
namespace Formed
variable {O L I J k p n g j h} (H : O.Formed L I J k p n g j h)
    (KY : QuantifierRoute L.witnesses C L.base j) (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (O.rename e.names).Formed (L.rename e) I J k p n g j h :=
  ⟨H.relational.rename e,H.inner.rename e,H.outer.rename e⟩
end Formed
end ObservationCode

end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (B : SpecializedCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
namespace Formed
variable {B L I J k p n g j h} (H : B.Formed L I J k p n g j h)
    (KY : QuantifierRoute L.witnesses C L.base j) (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (B.rename e.names).Formed (L.rename e) I J k p n g j h := by
  refine ⟨H.observation.rename e,e.typing H.type_sorted,e.moded H.type_mode,?_,?_,?_⟩
  · have hh := congrArg (Expr.rename e.names) H.shape
    simpa only [yType_rename,ChannelCode.logicalType_rename,baseType_rename,SpecializedCode.rename,
      relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hh
  · exact congrArg (DataWrapper.rename e.names) H.outer_second_shape
  · have hh := congrArg (Expr.rename e.names) H.outer_first_shape
    simpa only [DataWrapper.apply_rename,ThreeCopyCode.middleType_rename,ProbeCode.carrier_rename,
      baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,ObservationCode.copies,
      RelationalCode.rename,DoubleCode.rename,ThreeCopyCode.rename,ProbeCode.rename] using hh

end Formed
end

variable (B : SpecializedCode S)

theorem property_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (ρ : Nat → Nat) :
    (B.property L KY KP t v).rename ρ = (B.rename ρ).property (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  fin_cases t <;> simp only [property,propertyG_rename,propertyC_rename,propertyE_rename,propertyR_rename]
theorem property_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (σ : Nat → Expr S) :
    (B.property L KY KP t v).subst σ = (B.subst σ).property (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  fin_cases t <;> simp only [property,propertyG_subst,propertyC_subst,propertyE_subst,propertyR_subst]
theorem propertyBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (ρ : Nat → Nat) :
    (B.propertyBody L KY KP t).rename (Expr.liftRen ρ) =
      (B.rename ρ).propertyBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t := by
  simp only [propertyBody,property_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem propertyBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :
    (B.propertyBody L KY KP t).instantiate v = B.property L KY KP t v := by
  simp only [propertyBody,Expr.instantiate,property_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst,Expr.single]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem propertyBody_family_oai (t : Fin 7) : L.Family B.predType (B.propertyBody L.code KY.code KP.code t) := by
  intro Δ δ e v hv mv
  rw [propertyBody_rename,propertyBody_instantiate]
  exact (H.rename e).property_formula (KY.rename e) (KP.rename e) t (by simpa only [predType_rename] using hv) mv

end Formed
end SpecializedCode
end PureTypeSystem.Labelled

end OAI
end

theorem solution.{u} : type_of% @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family_oai.{u} := @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family_oai.{u}
