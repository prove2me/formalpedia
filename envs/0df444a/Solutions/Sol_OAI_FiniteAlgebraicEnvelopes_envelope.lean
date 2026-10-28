-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.envelope
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T19:55:36.290247+00:00
-- url     : https://prove2.me/submissions/1aed83f0-69f4-402c-b142-129635807b24

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_OAIFAE004

section
-- module Solutions.OAIFAE.Steinberg
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Nonunital correction, Steinberg groups, corners, and kernel annihilation.
-/


namespace FiniteAlgebraicEnvelopes

universe u


/-! The correction for a nonunital coefficient map in the affine transition and product identities.
The proof works over a noncommutative ring. -/


section NonunitalCorrection
variable {R S : Type*} [Ring R] [Ring S]

theorem correctedMap_injective (ψ : R →ₙ+* S) (hψ : Function.Injective ψ) :
    Function.Injective (correctedMap ψ) := by
  intro x y h
  have hsub : x - 1 = y - 1 := hψ (add_left_cancel h)
  exact sub_left_inj.mp hsub

end NonunitalCorrection


/-! The Steinberg presentation in the Steinberg kernel argument.  No stability or centrality
 theorem is assumed.  Root indices are restricted to the off-diagonal. -/

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Affine
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.FiniteAlgebraicEnvelopes.Steinberg.instNormalGroupFinOfNatNatRingKernel _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.freeAlgebra_finitelyPresented _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.polynomial_finitelyPresented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Rank-six affine relations, modules, and finite affine presentations.
-/


/- The rank-six affine presentation. -/
namespace FiniteAlgebraicEnvelopes

namespace FiniteAffine
open scoped commutatorElement
variable {R : Type*} [Ring R]

variable (F D : Finset R) (h1 : (1:R) ∈ F) (hgen : Subring.closure (↑F : Set R) = ⊤)

theorem finitelyPresented [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)] :
    Group.IsFinitelyPresented (Presentation F D) := by
  apply Group.IsFinitelyPresented.quotient (N F D)
  refine ⟨relators F D, ?_, rfl⟩
  exact (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)


include h1 hgen in
theorem affine_finitelyPresented [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)] :
    Group.IsFinitelyPresented (AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R))) := by
  let := finitelyPresented F D
  exact Group.IsFinitelyPresented.equiv (equivalence F D h1 hgen)

end FiniteAffine
end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Enveloping
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.FiniteAlgebraicEnvelopes.Steinberg.instNormalGroupFinOfNatNatRingKernel _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.freeAlgebra_finitelyPresented _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.polynomial_finitelyPresented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Tensor-enveloping algebra actions, simplicity, and elementary row control.
-/


namespace FiniteAlgebraicEnvelopes.Enveloping
open scoped TensorProduct
variable (k B : Type*) [CommRing k] [Ring B] [Algebra k B]

variable {k B}

section Simple
variable {A : Type*} [Ring A] [Algebra k A] [IsSimpleRing A]

/-- Simplicity supplies every desired row operation. -/
theorem coefficient_control (i : A →ₙₐ[k] B) (u d : A) (hu : u ≠ 0) :
    ∃ r : Coeff k B, r • i u = i d := by
  have huI : u ∈ reachable i u := by
    simp only [reachable,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq]
    exact ⟨1,one_smul _ _⟩
  have hI : reachable i u ≠ ⊥ := by
    intro h
    rw [h] at huI
    exact hu (by simpa using huI)
  have htop : reachable i u = ⊤ := (eq_bot_or_eq_top _).resolve_left hI
  have hd : d ∈ reachable i u := by rw [htop]; trivial
  simpa only [reachable,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq] using hd
end Simple

end FiniteAlgebraicEnvelopes.Enveloping


namespace FiniteAlgebraicEnvelopes.RowControl
open Enveloping
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B] [IsSimpleRing A]

theorem act_mul (g h : Steinberg.Group (Fin 6) (Coeff k B)) (v : Fin 6 → B) :
    act (g*h) v = act g (act h v) := by simp [act]

omit [IsSimpleRing A] in
theorem Related.refl (i : A →ₙₐ[k] B) (v : Fin 6 → A) : Related i v v := ⟨1,act_one _⟩
omit [IsSimpleRing A] in
theorem Related.trans {i : A →ₙₐ[k] B} {u v w : Fin 6 → A}
    (huv : Related i u v) (hvw : Related i v w) : Related i u w := by
  obtain ⟨g,hg⟩ := huv
  obtain ⟨h,hh⟩ := hvw
  exact ⟨h*g,by rw [act_mul,hg,hh]⟩
omit [IsSimpleRing A] in
theorem Related.symm {i : A →ₙₐ[k] B} {v w : Fin 6 → A}
    (h : Related i v w) : Related i w v := by
  obtain ⟨g,hg⟩ := h
  refine ⟨g⁻¹,?_⟩
  rw [← hg,← act_mul,inv_mul_cancel,act_one]

/-- A genuine Steinberg element sets any nonpivot row to the desired value. -/
theorem set_row (i : A →ₙₐ[k] B) (v : Fin 6 → A) (j l : Fin 6)
    (hj : v j ≠ 0) (hl : l ≠ j) (a : A) : Related i v (Function.update v l a) := by
  obtain ⟨r,hr⟩ := coefficient_control i (v j) (a-v l) hj
  refine ⟨Steinberg.root l j hl r,?_⟩
  rw [act_root]
  funext b
  by_cases hb : b=l
  · subst b
    simp [hr]

  · simp [hb]

/-- Eliminate any finite set of rows around a fixed nonzero pivot. -/
theorem set_rows (i : A →ₙₐ[k] B) (v w : Fin 6 → A) (j : Fin 6)
    (hj : v j ≠ 0) (s : Finset (Fin 6)) (hs : j ∉ s) :
    Related i v (fun a => if a ∈ s then w a else v a) := by
  induction s using Finset.induction_on with
  | empty => simpa using Related.refl i v
  | @insert a s ha ih =>
    have hjs : j ∉ s := fun h => hs (Finset.mem_insert_of_mem h)
    have hja : j ≠ a := fun h => hs (by simp [h])
    have hvj : (if j ∈ s then w j else v j) ≠ 0 := by simpa [hjs] using hj
    have hstep := set_row i (fun b => if b ∈ s then w b else v b) j a hvj hja.symm (w a)
    have he : Function.update (fun b => if b ∈ s then w b else v b) a (w a) =
        fun b => if b ∈ insert a s then w b else v b := by
      funext b
      by_cases hb : b=a
      · subst b; simp
      · simp [hb]
    rw [he] at hstep
    exact (ih hjs).trans hstep

/-- Every nonzero vector in the simple-algebra image reaches the same standard column. -/
theorem normalize (i : A →ₙₐ[k] B) (v : Fin 6 → A) (hv : v ≠ 0) :
    Related i v (Pi.single 5 1) := by
  have hex : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨j,hj⟩ := hex
  have hp : ∃ w : Fin 6 → A, Related i v w ∧ w 5 = 1 := by
    by_cases hj5 : j=5
    · subst j
      let u := Function.update v 0 1
      have h₁ : Related i v u := set_row i v 5 0 hj (by decide) 1
      have hu : u 0 ≠ 0 := by simp [u]
      refine ⟨Function.update u 5 1,h₁.trans (set_row i u 0 5 hu (by decide) 1),?_⟩
      simp
    · refine ⟨Function.update v 5 1,set_row i v j 5 hj (Ne.symm hj5) 1,?_⟩
      simp
  obtain ⟨w,hw,hw5⟩ := hp
  have hwne : w 5 ≠ 0 := by rw [hw5]; exact one_ne_zero
  have hkill := set_rows i w (fun _ => 0) 5 hwne (Finset.univ.erase 5) (by simp)
  have he : (fun a => if a ∈ Finset.univ.erase (5:Fin 6) then (0:A) else w a) =
      Pi.single 5 1 := by
    funext a
    by_cases ha : a=5
    · subst a; simp [hw5]
    · simp [ha]
  rw [he] at hkill
  exact hw.trans hkill

/-- The linear core of two-transitivity, with actual root words. -/
theorem transitive_nonzero (i : A →ₙₐ[k] B) (v w : Fin 6 → A)
    (hv : v ≠ 0) (hw : w ≠ 0) : Related i v w :=
  (normalize i v hv).trans (normalize i w hw).symm
end FiniteAlgebraicEnvelopes.RowControl

end OAI
end

section
-- module Solutions.OAIFAE.Contracted
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Contracted monoid algebras, selectors, and the simplicity criterion.
-/


namespace FiniteAlgebraicEnvelopes.Contracted
open MonoidAlgebra
open scoped Classical
noncomputable section
variable (k H : Type*) [CommRing k] [MonoidWithZero H]

variable {k H}

/-- The quotient retains exactly the nonzero monoid coefficients. -/
theorem exists_nonzero_coeff (f : MonoidAlgebra k H) (hf : quotient k H f ≠ 0) :
    ∃ h : H, h ≠ 0 ∧ f.coeff h ≠ 0 := by
  by_contra! h
  apply hf
  change quotient k H f = quotient k H 0
  rw [quotient_eq]
  intro a ha
  simpa using h a ha

/-- Expansion in the exact contracted monoid basis. -/
theorem expansion (f : MonoidAlgebra k H) :
    quotient k H f = f.coeff.sum (fun h c => basis k H h c) := by
  conv_lhs => rw [← sum_coeff_single f]
  simp only [Finsupp.sum,map_sum,basis]

/-- The selector sandwich extracts a single nonzero coefficient. -/
theorem sandwich (f : MonoidAlgebra k H) (h L R : H)
    (he : L*h*R=1) (hz : ∀ g ∈ f.coeff.support, g ≠ h → L*g*R=0) :
    basis k H L 1 * quotient k H f * basis k H R 1 =
      algebraMap k (Algebra k H) (f.coeff h) := by
  classical
  rw [expansion]
  simp only [Finsupp.sum,Finset.mul_sum,Finset.sum_mul,basis_mul,one_mul,mul_one]
  rw [Finset.sum_eq_single h]
  · rw [he,basis_one]
  · intro g hg hgh
    rw [hz g hg hgh,basis_zero]
  · intro hh
    have hf : f.coeff h = 0 := Finsupp.notMem_support_iff.mp hh
    simp [hf]

theorem coefficient_ext {x y : Algebra k H}
    (h : ∀ a (ha : a ≠ 0), coefficient a ha x = coefficient a ha y) : x=y := by
  induction x using Quotient.inductionOn with | h f =>
    induction y using Quotient.inductionOn with | h g =>
      exact (quotient_eq k H f g).mpr h

section Embedded
variable {J : Type*} [MonoidWithZero J]
variable (c : H →ₙ* J)

/-- Every nonzero coefficient is retained at its distinct new basis element. -/
theorem coefficient_embedding (hc : Function.Injective c) (hz : ∀ h, c h ≠ 0)
    (h : H) (hh : h ≠ 0) (x : Algebra k H) :
    coefficient (c h) (hz h) (embedding (k:=k) c x) = coefficient h hh x := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change coefficient (c h) (hz h) (embedding c (quotient k H f)) =
    coefficient h hh (quotient k H f)
  induction f using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => simpa only [map_add] using congrArg₂ (·+·) hf hg
    | single g r =>
      change coefficient (c h) (hz h) (embedding (k:=k) c (basis k H g r)) = coefficient h hh (basis k H g r)
      rw [embedding_basis,map_smul,map_sub,coefficient_basis,coefficient_basis]
      have hne : c h ≠ c 0 := fun he => hh (hc he)
      simp only [ite_eq_right hne,sub_zero,coefficient_basis]
      by_cases he : h=g
      · subst g; simp
      · simp [he,hc.eq_iff]

theorem embedding_injective (hc : Function.Injective c) (hz : ∀ h, c h ≠ 0) :
    Function.Injective (embedding (k:=k) c) := by
  intro x y hxy
  apply coefficient_ext
  intro h hh
  rw [← coefficient_embedding c hc hz h hh,← coefficient_embedding c hc hz h hh,hxy]

/-- The unit of B is outside the entire embedded subalgebra, not only different from e. -/
theorem one_not_mem_range [Nontrivial k] [Nontrivial J] (hc : ∀ h, c h ≠ 1) :
    (1 : Algebra k J) ∉ Set.range (embedding (k:=k) c) := by
  rintro ⟨x,hx⟩
  have hz : coefficient (k:=k) (1:J) one_ne_zero (embedding c x) = 0 := by
    clear hx
    obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
    change coefficient (1:J) one_ne_zero (embedding c (quotient k H f)) = 0
    induction f using MonoidAlgebra.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add,hf,hg,add_zero]
      | single h r =>
        change coefficient (1:J) one_ne_zero (embedding c (basis k H h r)) = 0
        rw [embedding_basis,map_smul,map_sub,coefficient_basis,coefficient_basis]
        simp [Ne.symm (hc h),Ne.symm (hc 0)]
  rw [hx] at hz
  have hone : coefficient (k:=k) (1:J) one_ne_zero 1 = 1 :=
    (coefficient_basis (k:=k) (1:J) one_ne_zero 1 1).trans (ite_eq_left rfl)
  rw [hone] at hz
  exact one_ne_zero hz

end Embedded


section Field
variable {K : Type*} [Field K] {H : Type*} [MonoidWithZero H] [Nontrivial H]

/-- The simplicity argument for contracted monoid algebras over any coefficient field. -/
theorem simple_of_selectors (hS : Selectors H) : IsSimpleRing (Algebra K H) := by
  classical
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I=⊥
  · exact Or.inl hI
  right
  rw [← I.one_mem_iff]
  obtain ⟨a,ha,ha0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  obtain ⟨f,rfl⟩ := (zeroIdeal K H).ringCon.mkₐ_surjective (α:=K) a
  obtain ⟨h,hh,hfh⟩ := exists_nonzero_coeff f ha0
  have hmem : h ∈ f.coeff.support.erase 0 := by simp [hh,Finsupp.mem_support_iff,hfh]
  obtain ⟨L,R,he,hz⟩ := hS (f.coeff.support.erase 0) (by simp) h hmem
  have hz' : ∀ g ∈ f.coeff.support, g ≠ h → L*g*R=0 := by
    intro g hg hgh
    by_cases hg0 : g=0
    · simp [hg0]
    · exact hz g (by simp [hg,hg0]) hgh
  have hc : algebraMap K (Algebra K H) (f.coeff h) ∈ I := by
    rw [← sandwich f h L R he hz']
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)
  have hi := I.mul_mem_left (algebraMap K (Algebra K H) (f.coeff h)⁻¹) _ hc
  simpa only [← map_mul,inv_mul_cancel₀ hfh,map_one] using hi
end Field

end
end FiniteAlgebraicEnvelopes.Contracted


/- Finite weak components and bounded normalization for the finite compiler. -/

end OAI
end

section
-- module Solutions.OAIFAE.Normalization
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.kFG _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableLetter _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableShape _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableHeadOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableHeadOfFintype_1 _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableInstruction _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H B T K : Type*}

namespace Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path

 theorem rule_length (table : Table H B T) (m : H → K) {u v : List (Letter (B×T) K)}
    (h : Rule table m u v) : u.length = 2 ∧ v.length = 2 := by
  cases h with
  | cell q b t i h =>
    cases hd : table.direction q <;> cases hc : i.cross <;>
      simp [headed,inLeft,inRight,outLeft,outRight]
  | left => simp
  | right => simp

end Literal
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {S Γ Q : Type*}

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

 theorem ordinary_length {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) :
    u.length ≤ 4 ∧ v.length ≤ 4 := by
  cases h with
  | internal h => obtain ⟨h₁,h₂⟩ := Scan.Literal.rule_length _ _ h; omega
  | clean c => cases he : Cleanup.emit c <;> simp
  | raw => simp
  | merge => simp
  | quota => simp
  | entry => simp
  | finish => simp

 theorem rule_length {u v : List (Letter S Γ Q)} (h : Rule A M u v) :
    u.length ≤ 4 ∧ v.length ≤ 4 := by
  cases h with
  | ordinary h => exact ordinary_length A M h
  | zero h => cases h; simp
  | exit => simp

/-- The source presentation is finite, not a schema depending on arbitrary
    sector contexts. Every defining side has at most four letters. -/
theorem rules_finite [Fintype S] [Fintype Γ] [Fintype Q] :
    {p : List (Letter S Γ Q) × List (Letter S Γ Q) | Rule A M p.1 p.2}.Finite := by
  apply ((List.finite_length_le (Letter S Γ Q) 4).prod
    (List.finite_length_le (Letter S Γ Q) 4)).subset
  rintro ⟨u,v⟩ h
  exact rule_length A M h

end

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word

open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem present_nil_ne_omega
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} (h : ∀ m, RawRuns.Budget f m) (hcomp : ∀ m, ComputesAt A M f m) :
    present A M [] ≠ present A M [.zero] := by
  intro he
  have hh := (present_eq_iff_normal A M hdecode h hcomp [] [.zero]).mp he
  simp at hh

end FiniteAlgebraicEnvelopes.Compiler.Word

/- The actual partial evaluator is a finite plan followed by partial calls.
   Its definition has no budget and does not totalize an undefined program. -/

end OAI
end

section
-- module Solutions.OAIFAE.Selectors
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/

namespace FiniteAlgebraicEnvelopes.Bootstrap.Selectors

section
variable {S : Type*} [DecidableEq S] [Primcodable S]

 theorem tuples_complete (z : S) {ws : List (List S)}
    (hne : ws≠[]) (hd : ws.Nodup) (hz : ∀ w∈ws,z∉w) : tuples z (Encodable.encode ws)=ws := by
  simp only [tuples,Encodable.encodek,Option.getD_some]
  exact ite_eq_left ⟨hne,hd,hz⟩

end

end FiniteAlgebraicEnvelopes.Bootstrap.Selectors

end OAI
end

section
-- module Solutions.OAIFAE.Quotients
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.hFG _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.kFG _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap

section

open Relation

namespace Selectors
variable {S : Type*} [DecidableEq S] {a : Markers S}

theorem process_mono (base : List (List S × List S)) (stages : ℕ → Stage S)
    (n : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    ∀ p∈process (a:=a) base stages n j,p∈process (a:=a) base stages n k := by
  induction hjk with
  | refl => exact fun _ h => h
  | @step k h ih =>
    exact fun p hp => choose_contains _ _ _ p (ih p hp)

theorem selected_mem {base : List (List S × List S)} {stages : ℕ → Stage S}
    {n j : ℕ} (hjn : j<n) (hs : (stages j).size≤n)
    (ha : allowed (process (a:=a) base stages n j) (stages j)=true) :
    ∀ p∈rules a (stages j).size (stages j).bodies,p∈process (a:=a) base stages n n := by
  intro p hp
  apply process_mono base stages n (Nat.succ_le_of_lt hjn) p
  change p∈choose (a:=a) (process base stages n j) (stages j) n
  rw [choose,ite_eq_left ⟨hs,ha⟩]
  exact List.mem_append_right _ hp
end Selectors

namespace Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

theorem normal_irreducible (w : List S) {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈T n) (hwlen : w.length≤n) : Irreducible (Step rs) (normal T w) := by
  have hw := normal_mem T wf good stable w
  rw [tableNormal_at wf (fun k _ => good k)
    (fun k hk => stable k _ hk) hrs hwlen] at hw
  exact (evaluate_sound hw).2

 theorem representative_injective : Function.Injective (representative T) := by
  intro x y he
  rw [←present_representative T wf good stable x,←present_representative T wf good stable y,he]

 theorem representative_irreducible (x : Mon T) {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈T n) (hx : (representative T x).length≤n) :
    Irreducible (Step rs) (representative T x) := by
  have h := normal_irreducible T wf good stable (representative T x) hrs hx
  simpa only [representative,normal_idempotent T wf good stable] using h

 theorem present_nil_ne_zero (z : S)
    (hshort : ∀ n rs,rs∈T n → ∀ p∈rs,1<p.1.length) :
    (1 : Mon T)≠present T [z] := by
  obtain ⟨r0,hr0,_⟩ := good 0
  obtain ⟨r1,hr1,_⟩ := good 1
  have h0 : normal T []=[] := normal_eq_self T wf good stable hr0
    (irreducible_of_short (fun p hp => by simpa using Nat.lt_trans Nat.zero_lt_one (hshort 0 r0 hr0 p hp)))
  have h1 : normal T [z]=[z] := normal_eq_self T wf good stable hr1
    (irreducible_of_short (fun p hp => hshort 1 r1 hr1 p hp))
  intro he
  have hh := (present_eq_iff T wf good stable [] [z]).mp he
  rw [h0,h1] at hh
  simp at hh

 theorem representative_avoids_zero (z : S) (x : Mon T)
    (hx : x≠present T [z])
    (hz : ∀ n rs,rs∈T n → Absorbs rs z) : z∉representative T x := by
  intro hzx
  let w := representative T x
  obtain ⟨rs,hrs,hd,_⟩ := good w.length
  have he := present_steps T hrs hd le_rfl (absorbs_mem (hz _ _ hrs) hzx)
  exact hx ((present_representative T wf good stable x).symm.trans he)

end Quotient
end

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap.Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

variable {Γ Q : Type*} [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q] [LinearOrder (Compiler.Control.Sector S Γ Q)]
variable (A : Compiler.Simulator.Alphabet S Γ) (M : Compiler.Simulator.Machine Q Γ)
variable (hdecode : ∀ g a,A.output g=some a → g=A.input a)
variable (hr : Compiler.Word.Realizes A M (tableNormal T))

include hdecode hr in
theorem rawMap_injective : Function.Injective (rawMap T wf good stable A M hdecode hr) := by
  intro x y hxy
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n)) _ _).mp hxy
  simp only [Compiler.Word.normal_raw] at hn
  have he := congrArg Compiler.Word.rawLetters hn
  simp only [Compiler.Word.rawLetters_raw] at he
  exact representative_injective T wf good stable he

include hdecode hr in
theorem rawMap_ne_one (x : Mon T) : rawMap T wf good stable A M hdecode hr x≠1 := by
  intro hx
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n))
    (Compiler.Word.raw A.blank (representative T x)) []).mp hx
  simp only [Compiler.Word.normal_raw,Compiler.Word.normal_nil] at hn
  simp [Compiler.Word.raw,Compiler.Word.encode,Compiler.Surface.raw,Compiler.Scan.literal,
    Compiler.Path.encode,Compiler.Path.headed] at hn

include hdecode hr in
theorem rawMap_ne_zero (x : Mon T) :
    rawMap T wf good stable A M hdecode hr x≠Compiler.Word.present A M [.zero] := by
  intro hx
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n))
    (Compiler.Word.raw A.blank (representative T x)) [.zero]).mp hx
  simp only [Compiler.Word.normal_raw,Compiler.Word.normal_omega] at hn
  simp [Compiler.Word.raw,Compiler.Word.encode,Compiler.Surface.raw,Compiler.Scan.literal,
    Compiler.Path.encode,Compiler.Path.headed] at hn

end Bootstrap.Quotient
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation
variable {S : Type*}

namespace Quotient
variable [DecidableEq S] {A M : Type*} [Monoid M]
variable {T : ℕ → Part (List (List S × List S))} (C : BlockCode A S)

variable (e : FreeMonoid A →* M) (he : Function.Surjective e)
  (hc : ∀ u v : List A,present T (C.encode u)=present T (C.encode v) ↔
    e (FreeMonoid.ofList u)=e (FreeMonoid.ofList v))

omit [DecidableEq S] in
theorem descendCode_injective : Function.Injective (descendCode C e he hc) := by
  intro x y h
  exact (he x).choose_spec.symm.trans (((hc _ _).mp h).trans (he y).choose_spec)
end Quotient

end

variable {S : Type*}

namespace Separator

theorem split_injective {z : S} {u v u' v' : List S}
    (hu : z∉u) (hu' : z∉u') (he : u++z::v=u'++z::v') : u=u' ∧ v=v' := by
  induction u generalizing u' with
  | nil =>
    cases u' with
    | nil => exact ⟨rfl,(List.cons.inj he).2⟩
    | cons a u' =>
      have ha : z=a := (List.cons.inj he).1
      exact False.elim (hu' (by simp [ha]))
  | cons a u ih =>
    cases u' with
    | nil =>
      have ha : a=z := (List.cons.inj he).1
      exact False.elim (hu (by simp [ha]))
    | cons b u' =>
      obtain ⟨rfl,hrest⟩ := List.cons.inj he
      obtain ⟨rfl,hv⟩ := ih (fun h => hu (List.mem_cons_of_mem _ h))
        (fun h => hu' (List.mem_cons_of_mem _ h)) hrest
      exact ⟨rfl,hv⟩
end Separator

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (zero sep : S)

omit [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q] [Std.Trichotomous r] in
theorem separator_literal_injective (hs : sep∉C.Alphabet)
    {u v u' v' : List A}
    (he : C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v)=
      C.encode (Canonical.least wf q u')++sep::C.encode (Canonical.least wf q v')) :
    q u=q u' ∧ q v=q v' := by
  have hh := Separator.split_injective (fun h => hs (C.mem_alphabet h))
    (fun h => hs (C.mem_alphabet h)) he
  have hu := C.encode_injective hh.1
  have hv := C.encode_injective hh.2
  exact ⟨(Canonical.least_class wf q u).symm.trans
    ((congrArg q hu).trans (Canonical.least_class wf q u')),
    (Canonical.least_class wf q v).symm.trans
    ((congrArg q hv).trans (Canonical.least_class wf q v'))⟩
end Static

namespace Quotient
variable [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {t : S → S → Prop} (wt : WellFounded t)
  (good : ∀ n,GoodTable (r:=t) T n)
  (stable : ∀ k n,k≤n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
  {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (zero sep : S)
variable (hshort : ∀ n rs,rs∈T n → ∀ p∈rs,1<p.1.length)
variable (hiso : ∀ n rs,rs∈T n → ∀ p∈rs,p∈Static.table C wf q zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep)
variable (hstatic : ∀ n rs,rs∈T ((C.width+1)*n) → ∀ p∈Static.table C wf q zero n,p∈rs)
variable (hc : ∀ n,Static.Contextual q n) (hi : ∀ n,Static.ZeroIdeal q n) (hzero : q []≠none)
variable (hs : sep∉C.Alphabet)
include wt good stable hshort hiso hstatic hc hi hzero hs

omit [DecidableEq A] [DecidableEq Q] in
theorem present_separator_iff {u v u' v' : List A}
    (hu : q u≠none) (hv : q v≠none) (hu' : q u'≠none) (hv' : q v'≠none) :
    present T (C.encode u++sep::C.encode v)=present T (C.encode u'++sep::C.encode v') ↔
      q u=q u' ∧ q v=q v' := by
  rw [present_eq_iff T wt good stable,
    normal_separator T wt good stable C wf q zero sep hshort hiso hstatic hc hi hzero hs hu hv,
    normal_separator T wt good stable C wf q zero sep hshort hiso hstatic hc hi hzero hs hu' hv']
  constructor
  · exact Static.separator_literal_injective C wf q sep hs
  · rintro ⟨hu,hv⟩
    rw [Canonical.least_congr wf q hu,Canonical.least_congr wf q hv]

end Quotient

end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.PartialAffine
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine

 theorem tail_injective : Function.Injective tail := by
  intro r s h
  have hr := congrFun h (some r)
  have hs := congrFun h (some s)
  simp only [tail,Option.bind_some,le_refl,↓reduceIte] at hr hs
  have hsr : s ≤ r := by by_contra hn; simp [hn] at hr
  have hrs : r ≤ s := by by_contra hn; simp [hn] at hs
  exact le_antisymm hrs hsr

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIFAE.MonoidAlgebras
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.bigAlgebra_countable _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.columnSpace_countable _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

end

open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace Selectors
variable {S : Type*} [DecidableEq S] [Primcodable S]

/-- Every nonzero irreducible ordered tuple receives its literal selector.
    The finite processing stage is chosen beyond the complete selector word. -/
theorem tuple_selected_rulesEq (a : Markers S) (T : ℕ → Part (List (List S × List S)))
    (bases : ℕ → List (List S × List S))
    (hT : ∀ n,∃ rs∈T n,RulesEq rs (process (a:=a) (bases n) (stages a.zero) n n))
    {ws : List (List S)} (hne : ws≠[]) (hd : ws.Nodup) (hz : ∀ w∈ws,a.zero∉w)
    (hi : ∀ w∈ws,∀ n rs,rs∈T n → w.length≤n → Irreducible (Step rs) w) :
    ∃ N,∀ w∈ws,Quotient.present T (a.wrap N w)=
      Quotient.present T (if ws.head?=some w then [] else [a.zero]) := by
  let j := Encodable.encode ws
  let N := sizes a.zero j
  let n := 3*N+2
  have he : (stages a.zero j).bodies=ws := tuples_complete a.zero hne hd hz
  have hsize : (stages a.zero j).size=N := rfl
  have hjN : j<N := index_lt_size a.zero j
  have hNn : N≤n := by omega
  have hjn : j<n := lt_of_lt_of_le hjN hNn
  have hlen (w : List S) (hw : w∈ws) : w.length<N := by
    apply body_lt_size a.zero j
    change w∈(stages a.zero j).bodies
    rw [he]
    exact hw
  obtain ⟨rs,hrs,heq⟩ := hT n
  have hall : allowed (process (a:=a) (bases n) (stages a.zero) n j) (stages a.zero j)=true := by
    apply allowed_iff.mpr
    intro w hw
    have hw' : w∈ws := he ▸ hw
    have nh := hi w hw' n rs hrs (le_trans (Nat.le_of_lt (hlen w hw')) hNn)
    intro v hv
    apply nh v
    rw [step_rulesEq heq]
    exact step_mono (process_mono (bases n) (stages a.zero) n (Nat.le_of_lt hjn)) hv
  refine ⟨N,?_⟩
  intro w hw
  have hp : (a.wrap N w,if ws.head?=some w then [] else [a.zero])∈rules a
      (stages a.zero j).size (stages a.zero j).bodies := by
    rw [he,hsize]
    exact (mem_rules a).mpr ⟨w,hw,rfl,rfl⟩
  have hmem := selected_mem hjn (hsize ▸ hNn) hall _ hp
  apply PresentedMonoid.mk_eq_mk_of_rel
  refine ⟨n,rs,hrs,(heq _).mpr hmem,?_⟩
  change (a.wrap N w).length≤n
  simp only [Markers.wrap,Envelopes.length_frame]
  have := hlen w hw
  omega

end Selectors
namespace Quotient
variable {S : Type*} [DecidableEq S] [Primcodable S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

/-- Source selectors for the stabilized quotient, with the distinguished element
    first in the tuple. Not an extra algebraic assumption on that quotient. -/
theorem selectors_rulesEq (a : Selectors.Markers S) (bases : ℕ → List (List S × List S))
    (hT : ∀ n,∃ rs∈T n,RulesEq rs (Selectors.process (a:=a) (bases n) (Selectors.stages a.zero) n n))
    (hz : ∀ n rs,rs∈T n → Absorbs rs a.zero)
    (X : Finset (Mon T)) (hX : present T [a.zero]∉X) (x : Mon T) (hx : x∈X) :
    ∃ L R : Mon T,L*x*R=1 ∧ ∀ y∈X,y≠x → L*y*R=present T [a.zero] := by
  classical
  let xs := x::(X.erase x).toList
  have xsne : xs≠[] := List.cons_ne_nil _ _
  have xsd : xs.Nodup := List.nodup_cons.mpr ⟨by simp,Finset.nodup_toList _⟩
  have xsmem (y : Mon T) : y∈xs ↔ y∈X := by
    simp only [xs,List.mem_cons,Finset.mem_toList,Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_,hh⟩)
      · exact hx
      · exact hh
    · intro hh
      by_cases he : y=x
      · exact Or.inl he
      · exact Or.inr ⟨he,hh⟩
  let rep := representative T
  have hrep : Function.Injective rep := representative_injective T wf good stable
  let ws := xs.map rep
  have hwsne : ws≠[] := by simp [ws,xs]
  have hwsd : ws.Nodup := xsd.map hrep
  have hwsz : ∀ w∈ws,a.zero∉w := by
    intro w hw
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
    exact representative_avoids_zero T wf good stable a.zero y
      (fun he => hX (he ▸ (xsmem y).mp hy)) hz
  have hwsi : ∀ w∈ws,∀ n rs,rs∈T n → w.length≤n → Irreducible (Step rs) w := by
    intro w hw n rs hrs hlen
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hw
    exact representative_irreducible T wf good stable y hrs hlen
  obtain ⟨N,hN⟩ := Selectors.tuple_selected_rulesEq a T bases hT hwsne hwsd hwsz hwsi
  let L := present T (a.d::List.replicate N a.l)
  let R := present T (List.replicate N a.r++[a.h])
  have heq (y : Mon T) : present T (a.wrap N (rep y))=L*y*R := by
    change present T (a.d::(List.replicate N a.l++rep y++List.replicate N a.r++[a.h]))=_
    have he : a.d::(List.replicate N a.l++rep y++List.replicate N a.r++[a.h])=
      (a.d::List.replicate N a.l)++rep y++(List.replicate N a.r++[a.h]) := by simp [List.append_assoc]
    rw [he,present_append,present_append,present_representative T wf good stable]
  refine ⟨L,R,?_,?_⟩
  · have hw : rep x∈ws := List.mem_map.mpr ⟨x,(xsmem x).mpr hx,rfl⟩
    have hs := hN _ hw
    rw [heq] at hs
    simpa only [ws,xs,List.map_cons,List.head?_cons,ite_true,present_nil] using hs
  · intro y hy hyx
    have hw : rep y∈ws := List.mem_map.mpr ⟨y,(xsmem y).mpr hy,rfl⟩
    have hs := hN _ hw
    rw [heq] at hs
    have hne : ws.head?≠some (rep y) := by
      simp only [ws,xs,List.map_cons,List.head?_cons]
      exact fun equality => hyx (hrep (Option.some.inj equality)).symm
    simpa only [ite_eq_right hne] using hs

end Quotient
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

theorem one_ne_zero_H : (1 : H s h)≠0 :=
  Quotient.present_nil_ne_zero (processor s h) wf_sigma (index_good s h) (index_stable s h) markers.zero
    (fun j _ hrs => tables_short s family.A family.M (index s h) j hrs)

instance hNontrivial : Nontrivial (H s h) := ⟨⟨1,0,one_ne_zero_H s h⟩⟩

theorem selectors_H (X : Finset (H s h)) (hX : (0:H s h)∉X) (x : H s h) (hx : x∈X) :
    ∃ L R : H s h,L*x*R=1 ∧ ∀ y∈X,y≠x → L*y*R=0 := by
  apply Quotient.selectors_rulesEq (processor s h) wf_sigma (index_good s h) (index_stable s h) markers
    (base s family.A family.M (index s h)) ?_ ?_ X hX x hx
  · intro j
    obtain ⟨rs,hrs,_⟩ := index_good s h j
    exact ⟨rs,hrs,tables_members s family.A family.M (index s h) j hrs⟩
  · intro j rs hrs
    exact tables_absorb s family.A family.M (index s h) j hrs

 theorem groupEmbedding_injective (hs : Subgroup.closure (Set.range s)=⊤) :
    Function.Injective (groupEmbedding s h hs) :=
  Quotient.descendCode_injective (finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)) (groupEval s)
    (groupEval_surjective s hs) (group_code_eq_iff s h)

attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instLinearOrderSectorSigmaProdBoolΓFamilyStateQIndex
theorem one_ne_zero_K : (1 : K s h)≠0 :=
  Word.present_nil_ne_omega KAlphabet (KMachine s h) family.decode
    (fun j => (index_budget s h j).totalize)
    (fun j => (family.realizes (index s h)).computesAt KAlphabet (KMachine s h) (index_budget s h j))

instance kNontrivial : Nontrivial (K s h) := ⟨⟨1,0,one_ne_zero_K s h⟩⟩

/-- The displayed literal presentation for K has a finite alphabet and finitely
    many relators; every side of a relator has length at most four. -/
theorem finite_relations_K :
    {p : List (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) ×
      List (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) |
        Word.Rule KAlphabet (KMachine s h) p.1 p.2}.Finite :=
  Word.rules_finite KAlphabet (KMachine s h)

theorem copyEmbedding_injective : Function.Injective (copyEmbedding s h) :=
  Quotient.rawMap_injective (processor s h) wf_sigma (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h)

theorem copyEmbedding_ne_one (x : H s h) : copyEmbedding s h x≠1 :=
  Quotient.rawMap_ne_one (processor s h) wf_sigma (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h) x

theorem copyEmbedding_ne_zero (x : H s h) : copyEmbedding s h x≠0 :=
  Quotient.rawMap_ne_zero (processor s h) wf_sigma (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h) x

theorem smallAlgebra_simple (𝕜 : Type*) [Field 𝕜] : IsSimpleRing (SmallAlgebra s h 𝕜) :=
  Contracted.simple_of_selectors (selectors_H s h)

theorem algebraEmbedding_injective (𝕜 : Type*) [CommRing 𝕜] [Nontrivial 𝕜] :
    Function.Injective (algebraEmbedding s h 𝕜) :=
  Contracted.embedding_injective (copyEmbedding s h) (copyEmbedding_injective s h) (copyEmbedding_ne_zero s h)

theorem one_not_in_smallAlgebra (𝕜 : Type*) [CommRing 𝕜] [Nontrivial 𝕜] :
    (1 : BigAlgebra s h 𝕜)∉Set.range (algebraEmbedding s h 𝕜) :=
  Contracted.one_not_mem_range (copyEmbedding s h) (copyEmbedding_ne_one s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.ContractedPresentation

variable (k S : Type*) [CommRing k]
variable (rel : FreeMonoid S → FreeMonoid S → Prop)
variable {M : Type*} [MonoidWithZero M] (e : PresentedMonoid rel ≃* M)
variable (z : FreeMonoid S) (hz : e (PresentedMonoid.mk rel z)=0)

theorem finite_relations (hrel : {p : FreeMonoid S × FreeMonoid S | rel p.1 p.2}.Finite) :
    {p : FreeAlgebra k S × FreeAlgebra k S | Rel k S rel z p.1 p.2}.Finite := by
  apply ((hrel.image (fun p => (word k S p.1, word k S p.2))).union
    (Set.finite_singleton (word k S z,0))).subset
  rintro ⟨a,b⟩ hab
  rcases hab with ⟨u,v,hu,rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inl ⟨(u,v),hu,rfl⟩
  · exact Or.inr rfl

end FiniteAlgebraicEnvelopes.ContractedPresentation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

theorem algebraRelations_finite :
    {p : FreeAlgebra k (AlgebraGenerators s h) × FreeAlgebra k (AlgebraGenerators s h) |
      AlgebraRelations s h k p.1 p.2}.Finite :=
  ContractedPresentation.finite_relations k (AlgebraGenerators s h) (Word.Rel KAlphabet (KMachine s h))
    [.zero] (finite_relations_K s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

section
namespace FiniteAlgebraicEnvelopes.ContractedPresentation
variable (k S : Type*) [CommRing k] (rel : FreeAlgebra k S → FreeAlgebra k S → Prop)

theorem quotientGenerators_generate : Algebra.adjoin k (Set.range (quotientGenerators k S rel))=⊤ := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift,AlgHom.range_eq_top]
  have he : FreeAlgebra.lift k (quotientGenerators k S rel)=RingQuot.mkAlgHom k rel := by
    apply FreeAlgebra.hom_ext
    funext x
    rw [Function.comp_apply,Function.comp_apply,FreeAlgebra.lift_ι_apply]
    rfl
  rw [he]
  exact RingQuot.mkAlgHom_surjective k rel

variable {A : Type*} [Ring A] [Algebra k A]

theorem equivalenceGenerators_generate (e : RingQuot rel ≃ₐ[k] A) :
    Algebra.adjoin k (Set.range (fun x => e (quotientGenerators k S rel x)))=⊤ := by
  rw [show Set.range (fun x => e (quotientGenerators k S rel x))=e '' Set.range (quotientGenerators k S rel) from Set.range_comp _ _]
  change Algebra.adjoin k (e.toAlgHom '' Set.range (quotientGenerators k S rel))=⊤
  rw [←AlgHom.map_adjoin,quotientGenerators_generate,Algebra.map_top,AlgHom.range_eq_top]
  exact e.surjective
end FiniteAlgebraicEnvelopes.ContractedPresentation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

theorem bigGenerators_finite : (bigGenerators s h k).Finite := Set.finite_range _

theorem bigGenerators_generate : Algebra.adjoin k (bigGenerators s h k)=⊤ :=
  ContractedPresentation.equivalenceGenerators_generate k _ _ (algebraPresentation s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

 theorem kappa_injective : Function.Injective (kappa s h) :=
  Quotient.descendCode_injective (TCode s h) (tEval s h) (tEval_surjective s h) (t_code_eq_iff s h)

end

open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

 theorem tTest_eq_iff (u v : List (TLetter s h)) :
    TTest s h u=TTest s h v ↔ tEval s h (FreeMonoid.ofList u)=tEval s h (FreeMonoid.ofList v) := by
  rw [tTest_eq_class,tTest_eq_class,tClass_eq_iff]

 attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instFintypeTLetter_1
theorem separator_injective : Function.Injective
    (fun p : {x : T s h // x≠0} × {x : T s h // x≠0} => kappa s h p.1*separator s h*kappa s h p.2) := by
  rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩ ⟨⟨x',hx'⟩,⟨y',hy'⟩⟩ he
  obtain ⟨u,rfl⟩ := tEval_surjective s h x
  obtain ⟨v,rfl⟩ := tEval_surjective s h y
  obtain ⟨u',rfl⟩ := tEval_surjective s h x'
  obtain ⟨v',rfl⟩ := tEval_surjective s h y'
  change kappa s h (tEval s h (FreeMonoid.ofList u.toList))*separator s h*kappa s h (tEval s h (FreeMonoid.ofList v.toList))=
    kappa s h (tEval s h (FreeMonoid.ofList u'.toList))*separator s h*kappa s h (tEval s h (FreeMonoid.ofList v'.toList)) at he
  rw [separator_word,separator_word] at he
  have hh := (Quotient.present_separator_iff (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero (6:Sigma)
    (fun j rs hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j rs hrs => tables_isolate_separator s h j hrs)
    (fun j rs hrs => tables_staticT s family.A family.M (index s h) j hrs)
    (fun j => (tTest_properties s h j).2.1) (fun j => (tTest_properties s h j).2.2)
    (tTest_properties s h 0).1
    (separator_avoid_T s h)
    (fun he => hx ((tTest_eq_none s h u.toList).mp he)) (fun he => hy ((tTest_eq_none s h v.toList).mp he))
    (fun he => hx' ((tTest_eq_none s h u'.toList).mp he)) (fun he => hy' ((tTest_eq_none s h v'.toList).mp he))).mp he
  exact Prod.ext (Subtype.ext ((tTest_eq_iff s h _ _).mp hh.1)) (Subtype.ext ((tTest_eq_iff s h _ _).mp hh.2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

section
namespace FiniteAlgebraicEnvelopes.Contracted
open MonoidAlgebra
variable {k H J : Type*} [CommRing k] [MonoidWithZero H] [MonoidWithZero J]

theorem coefficient_map (c : H →*₀ J) (hc : Function.Injective c)
    (h : H) (hh : h≠0) (x : Algebra k H) :
    coefficient (c h) (fun he => hh (hc (he.trans c.map_zero.symm))) (map (k:=k) c x)=coefficient h hh x := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change coefficient (c h) _ (map c (quotient k H f))=coefficient h hh (quotient k H f)
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simpa only [map_add] using congrArg₂ (·+·) hf hg
  | single g r =>
    change coefficient (c h) _ (map c (basis k H g r))=coefficient h hh (basis k H g r)
    rw [map_basis,coefficient_basis,coefficient_basis]
    congr 1
    exact propext hc.eq_iff

theorem map_injective (c : H →*₀ J) (hc : Function.Injective c) :
    Function.Injective (map (k:=k) c) := by
  intro x y he
  apply coefficient_ext
  intro h hh
  rw [←coefficient_map c hc h hh,←coefficient_map c hc h hh,he]
end FiniteAlgebraicEnvelopes.Contracted

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

theorem kappaAlgebra_injective (𝕜 : Type*) [CommRing 𝕜] : Function.Injective (kappaAlgebra s h 𝕜) :=
  Contracted.map_injective (kappa₀ s h) (kappa_injective s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.ZeroProduct
open scoped TensorProduct
open Contracted
variable (k K P : Type*) [CommRing k] [MonoidWithZero K] [Monoid P]

theorem tensorMap_linear : (tensorMap k K P).toLinearMap=(tensorLinearEquiv k K P).toLinearMap := by
  apply (tensorBasis k K P).ext
  rintro ⟨a,p⟩
  change tensorMap k K P ((tensorBasis k K P) (a,p))=tensorLinearEquiv k K P ((tensorBasis k K P) (a,p))
  rw [tensorLinearEquiv,Module.Basis.equiv_apply]
  simp only [tensorBasis,Module.Basis.tensorProduct_apply,monoidBasis_apply]
  change tensorMap k K P (basis k K a 1 ⊗ₜ[k] MonoidAlgebra.single p 1)=_
  rw [tensorMap_basis,one_mul]
  rfl

theorem tensorMap_bijective : Function.Bijective (tensorMap k K P) := by
  change Function.Bijective (tensorMap k K P).toLinearMap
  rw [tensorMap_linear]
  exact (tensorLinearEquiv k K P).bijective

end FiniteAlgebraicEnvelopes.ZeroProduct

end

end OAI
end

section
-- module Solutions.OAIFAE.Corners
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.bigAlgebra_countable _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.columnSpace_countable _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tensor embeddings and the nonunital corner maps between the two algebras.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine

 theorem E0_ne_E1 : E0≠E1 := by
  intro h
  have hh := congrArg Subtype.val h
  rw [E0_val,E1_val] at hh
  have := tail_injective hh
  norm_num at this

end FiniteAlgebraicEnvelopes.PartialAffine

section
namespace FiniteAlgebraicEnvelopes.PartialAffine.Corner
open scoped TensorProduct
variable (k B : Type*) [CommRing k] [Ring B] [Algebra k B]

 theorem coefficient0_q : coefficient0 k (q k)=1 := by
  change (q k).coeff E0 = 1
  simp [q,b,E0_ne_E1]

 theorem cornerRetract_cornerTensor (x : B) : cornerRetract k B (cornerTensor k B x)=x := by
  change TensorProduct.rid k B (TensorProduct.map (LinearMap.id : B →ₗ[k] B) (coefficient0 k) (x ⊗ₜ[k] q k))=x
  rw [TensorProduct.map_tmul,coefficient0_q]
  simp

 theorem cornerTensor_injective : Function.Injective (cornerTensor k B) :=
  Function.LeftInverse.injective (cornerRetract_cornerTensor k B)
end FiniteAlgebraicEnvelopes.PartialAffine.Corner

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

theorem rho_injective : Function.Injective (rho s h k) :=
  (kappaAlgebra_injective s h k).comp (ZeroProduct.tensorMap_bijective k (K s h) PartialAffine.monoid).1

theorem j_injective : Function.Injective (j s h k) :=
  (rho_injective s h k).comp (PartialAffine.Corner.cornerTensor_injective k (BigAlgebra s h k))

theorem phi_injective [Nontrivial k] : Function.Injective (phi s h k) :=
  (algebraEmbedding_injective s h k).comp (j_injective s h k)

 theorem phi_one_ne_one [Nontrivial k] : phi s h k 1≠1 := by
  intro he
  exact one_not_in_smallAlgebra s h k ⟨j s h k 1,he⟩

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open scoped TensorProduct
variable {k A B C D : Type*} [CommRing k] [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]

theorem map_injective [Module.Flat k B] [Module.Flat k C]
    (f : A →ₙₐ[k] B) (g : C →ₙₐ[k] D) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (map f g) :=
  TensorProduct.map_injective_of_flat_flat (f : A →ₗ[k] B) (g : C →ₗ[k] D) hf hg

theorem op_injective (f : A →ₙₐ[k] B) (hf : Function.Injective f) : Function.Injective (op f) := by
  intro x y he
  exact MulOpposite.unop_injective (hf (MulOpposite.op_injective he))

end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

open scoped TensorProduct
open Contracted
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

theorem separatorIndex_injective : Function.Injective (separatorIndex s h) := by
  intro a b he
  exact separator_injective s h (congrArg Subtype.val he)

 theorem separationLinear_basis (p : {a : T s h // a≠0} × {a : T s h // a≠0}) :
    separationLinear s h k ((monoidBasis (k:=k) (H:=T s h)).tensorProduct (monoidBasis (k:=k) (H:=T s h)) p)=
      monoidBasis (k:=k) (H:=H s h) (separatorIndex s h p) := by
  rw [Module.Basis.tensorProduct_apply',separationLinear_tmul]
  simp only [monoidBasis_apply,kappaAlgebra,map_basis,separatingElement,basis_mul,one_mul]
  rfl

 theorem separationLinear_injective : Function.Injective (separationLinear s h k) := by
  let b := (monoidBasis (k:=k) (H:=T s h)).tensorProduct (monoidBasis (k:=k) (H:=T s h))
  let v := fun p => monoidBasis (k:=k) (H:=H s h) (separatorIndex s h p)
  have hl : LinearIndependent k v :=
    (monoidBasis (k:=k) (H:=H s h)).linearIndependent.comp (separatorIndex s h) (separatorIndex_injective s h)
  have he : separationLinear s h k=b.constr k v := by
    apply b.ext
    intro p
    rw [Module.Basis.constr_basis]
    exact separationLinear_basis s h k p
  rw [he]
  exact b.injective_constr_of_linearIndependent hl

theorem jT_injective : Function.Injective (jT s h k) :=
  (ZeroProduct.tensorMap_bijective k (K s h) PartialAffine.monoid).1.comp
    (PartialAffine.Corner.cornerTensor_injective k (BigAlgebra s h k))

 theorem jT_apply (a : BigAlgebra s h k) : kappaAlgebra s h k (jT s h k a)=j s h k a := rfl

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

local instance smallFree : Module.Free k (BigAlgebra s h k) := Module.Free.of_basis (Contracted.monoidBasis (k:=k) (H:=K s h))
local instance oppositeFree : Module.Free k (BigAlgebra s h k)ᵐᵒᵖ :=
  Module.Free.of_basis ((Contracted.monoidBasis (k:=k) (H:=K s h)).map (MulOpposite.opLinearEquiv k))
local instance tFree : Module.Free k (TAlgebra s h k) := Module.Free.of_basis (Contracted.monoidBasis (k:=k) (H:=T s h))

theorem psi_injective [Nontrivial k] : Function.Injective (psi s h k) :=
  NonunitalTensor.map_injective _ _ (phi_injective s h k) (NonunitalTensor.op_injective _ (phi_injective s h k))

theorem detectionInput_injective : Function.Injective (detectionInput s h k) :=
  TensorProduct.map_injective_of_flat_flat _ _ (jT_injective s h k)
    ((jT_injective s h k).comp MulOpposite.unop_injective)

theorem detectionLinear_injective [Nontrivial k] : Function.Injective (detectionLinear s h k) :=
  (algebraEmbedding_injective s h k).comp
    ((separationLinear_injective s h k).comp (detectionInput_injective s h k))

theorem detectionLinear_eq : detectionLinear s h k=NonunitalTensor.actingLinear (phi s h k) (detectingElement s h k) := by
  apply TensorProduct.ext'
  intro a b
  change algebraEmbedding s h k
    (separationLinear s h k (jT s h k a⊗ₜ[k] jT s h k b.unop))=_
  rw [separationLinear_tmul,jT_apply,jT_apply,map_mul,map_mul]
  change phi s h k a*detectingElement s h k*phi s h k b.unop=_
  rw [←MulOpposite.op_unop b,NonunitalTensor.actingLinear_tmul]
  rfl

theorem detectionLinear_apply (r : R s h k) :
    detectionLinear s h k r=Enveloping.act k (BigAlgebra s h k) (psi s h k r) (detectingElement s h k) :=
  DFunLike.congr_fun (detectionLinear_eq s h k) r

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
end

section
-- module Solutions.OAIFAE.MappingTori
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.FiniteAlgebraicEnvelopes.SequentialLimit.countable_limit _root_.OAI.FiniteAlgebraicEnvelopes.SequentialLimit.torus_finitelyGenerated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Sequential limits, injective induced maps, and finite presentation of mapping tori.
-/


namespace FiniteAlgebraicEnvelopes.MappingTorus
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

theorem finite_relations [Group.FG Q] : (relations f).IsFinitelyNormallyGenerated := by
  obtain ⟨s, hs⟩ := Group.FG.out (G := Q)
  let N := Subgroup.normalClosure (relator f '' (s : Set Q))
  refine ⟨relator f '' (s : Set Q), s.finite_toSet.image _, ?_⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    exact Set.image_subset_range _ _
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, rfl⟩
    have hh : (MulAut.conj ((QuotientGroup.mk' N) letter)⁻¹).toMonoidHom.comp
        ((QuotientGroup.mk' N).comp Monoid.Coprod.inl) =
        ((QuotientGroup.mk' N).comp Monoid.Coprod.inl).comp f := by
      apply MonoidHom.eq_of_eqOn_dense hs
      intro y hy
      have hy' : (QuotientGroup.mk' N) (relator f y) = 1 := by
        apply (QuotientGroup.eq_one_iff _).mpr
        exact Subgroup.subset_normalClosure (Set.mem_image_of_mem _ hy)
      change ((QuotientGroup.mk' N) letter)⁻¹ *
        (QuotientGroup.mk' N) (Monoid.Coprod.inl y) * (QuotientGroup.mk' N) letter =
        (QuotientGroup.mk' N) (Monoid.Coprod.inl (f y))
      apply mul_inv_eq_one.mp
      simpa only [relator, map_mul, map_inv] using hy'
    apply (QuotientGroup.eq_one_iff _).mp
    have hx := DFunLike.congr_fun hh x
    change ((QuotientGroup.mk' N) letter)⁻¹ *
      (QuotientGroup.mk' N) (Monoid.Coprod.inl x) * (QuotientGroup.mk' N) letter =
      (QuotientGroup.mk' N) (Monoid.Coprod.inl (f x)) at hx
    change (QuotientGroup.mk' N) (relator f x) = 1
    simpa only [relator, map_mul, map_inv] using mul_inv_eq_one.mpr hx

theorem finitelyPresented [Group.IsFinitelyPresented Q] : Group.IsFinitelyPresented (Presentation f) := by
  have : Group.FG Q := by
    obtain ⟨n, q, hq, _⟩ := Group.IsFinitelyPresented.out (G := Q)
    exact Group.fg_of_surjective hq
  exact Group.IsFinitelyPresented.quotient (relations f) (finite_relations f)

theorem torus_finitelyPresented [Group.IsFinitelyPresented Q] :
    Group.IsFinitelyPresented (SequentialLimit.Torus f) := by
  let := finitelyPresented f
  exact Group.IsFinitelyPresented.equiv (equivalence f)

end FiniteAlgebraicEnvelopes.MappingTorus

end OAI
end

section
-- module Solutions.OAIFAE.SteinbergLimits
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.SequentialLimit.countable_limit _root_.OAI.FiniteAlgebraicEnvelopes.SequentialLimit.torus_finitelyGenerated _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.freeAlgebra_finitelyPresented _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.polynomial_finitelyPresented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Steinberg sequential limits, annihilated kernels, and injective torus maps.
-/

section
namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

theorem transition_injective (hf : Function.Injective f) (i j : ℕ) (hij : i≤j) :
    Function.Injective (transition f i j hij) := by
  change Function.Injective ((f^(j-i) : Monoid.End Q) : Q → Q)
  generalize j-i=n
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    rw [pow_succ']
    exact hf.comp ih

theorem of_injective (hf : Function.Injective f) (i : ℕ) : Function.Injective (of f i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x=1
  change of f i x=1 at hx
  obtain ⟨j,hij,he⟩ := (DirectLimit.exists_eq_one (G:=fun _ : ℕ => Q) (f:=transition f) ⟨i,x⟩).mp hx
  apply transition_injective f hf i j hij
  simpa only [map_one] using he

end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.Steinberg
variable {R : Type*} [Ring R]

theorem correctedUnits_injective (ψ : R →ₙ+* R) (hψ : Function.Injective ψ) :
    Function.Injective (correctedUnits ψ) := by
  intro a b he
  apply Units.ext
  apply correctedMap_injective (matrixNonunitalMap ψ) (by
    intro x y hxy
    ext i j
    exact hψ (congrFun (congrFun hxy i) j))
  exact congrArg Units.val he

theorem elementaryTransition_injective (ψ : R →ₙ+* R) (hψ : Function.Injective ψ) :
    Function.Injective (elementaryTransition ψ) := by
  intro a b he
  apply Subtype.ext
  exact correctedUnits_injective ψ hψ (congrArg Subtype.val he)

end FiniteAlgebraicEnvelopes.Steinberg
end

namespace FiniteAlgebraicEnvelopes.Steinberg

section
open scoped commutatorElement
variable {R : Type*} [Ring R]

theorem rootGenerators_finite {S : Set R} (hS : S.Finite) : (rootGenerators S).Finite :=
  (Set.toFinite (Set.univ : Set RootIndex) |>.prod (hS.insert 1)).image _

theorem root_mem_generators {S : Set R} (i j : Fin 6) (hij : i≠j) {r : R}
    (hr : r∈insert 1 S) : root i j hij r∈rootGenerators S :=
  ⟨(⟨(i,j),hij⟩,r),⟨Set.mem_univ _,hr⟩,rfl⟩

theorem rootGenerators_generate {S : Set R} (hS : Subring.closure S=⊤) :
    Subgroup.closure (rootGenerators S)=⊤ := by
  let H := Subgroup.closure (rootGenerators S)
  have h1 (i j : Fin 6) (hij : i≠j) : root i j hij (1:R)∈H :=
    Subgroup.subset_closure (root_mem_generators i j hij (Set.mem_insert 1 S))
  let C := coefficientSubring H h1
  have hSC : Subring.closure S≤C := Subring.closure_le.mpr (by
    intro r hr i j hij
    exact Subgroup.subset_closure (root_mem_generators i j hij (Set.mem_insert_of_mem 1 hr)))
  have hC (r : R) : r∈C := by rw [hS] at hSC; exact hSC (Subring.mem_top _)
  apply top_unique
  rw [←PresentedGroup.closure_range_of]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨⟨⟨i,j⟩,hij⟩,r⟩,rfl⟩
  exact hC r i j hij

theorem finitelyGenerated_of_ringGenerators {S : Set R} (hS : S.Finite)
    (hgen : Subring.closure S=⊤) : _root_.Group.FG (Group (Fin 6) R) :=
  _root_.Group.fg_iff.mpr ⟨rootGenerators S,rootGenerators_generate hgen,rootGenerators_finite hS⟩

variable [Algebra (ZMod 2) R]

theorem ringGenerators_of_algebraGenerators {S : Set R} (hS : Algebra.adjoin (ZMod 2) S=⊤) :
    Subring.closure S=⊤ := by
  let C : Subalgebra (ZMod 2) R := {
    toSubsemiring := (Subring.closure S).toSubsemiring
    algebraMap_mem' := by
      intro c
      have he : c=0 ∨ c=1 := by revert c; decide
      rcases he with rfl|rfl <;> simp }
  have hle : Algebra.adjoin (ZMod 2) S≤C := Algebra.adjoin_le (fun r hr => Subring.subset_closure hr)
  apply top_unique
  intro r hr
  have hc : r∈C := hle (by rw [hS]; trivial)
  exact hc

end

open scoped commutatorElement
variable {R : Type*} [Ring R]

variable (r : R → R → Prop)

theorem ringRelators_finite (hr : {p : R×R | r p.1 p.2}.Finite) : (ringRelators r).Finite := by
  have he : ringRelators r=(fun p : RootIndex×(R×R) =>
    root p.1.1.1 p.1.1.2 p.1.2 p.2.1*(root p.1.1.1 p.1.1.2 p.1.2 p.2.2)⁻¹) ''
    (Set.univ ×ˢ {p : R×R | r p.1 p.2}) := by
    ext z
    constructor
    · rintro ⟨i,j,hij,a,b,hab,rfl⟩
      exact ⟨(⟨(i,j),hij⟩,(a,b)),⟨Set.mem_univ _,hab⟩,rfl⟩
    · rintro ⟨⟨⟨⟨i,j⟩,hij⟩,⟨a,b⟩⟩,⟨_,hab⟩,rfl⟩
      exact ⟨i,j,hij,a,b,hab,rfl⟩
  rw [he]
  exact ((Set.toFinite (Set.univ : Set RootIndex)).prod hr).image _

/-- Finite ring equations require only finitely many additional Steinberg relators. -/
theorem ringQuot_finitelyPresented (hr : {p : R×R | r p.1 p.2}.Finite)
    [_root_.Group.IsFinitelyPresented (Group (Fin 6) R)] :
    _root_.Group.IsFinitelyPresented (Group (Fin 6) (RingQuot r)) := by
  have : _root_.Group.IsFinitelyPresented (RingQuotientGroup r) :=
    _root_.Group.IsFinitelyPresented.quotient (ringKernel r) ⟨ringRelators r,ringRelators_finite r hr,rfl⟩
  exact _root_.Group.IsFinitelyPresented.equiv (ringQuotEquivalence r)

end FiniteAlgebraicEnvelopes.Steinberg

end

end OAI
end

section
-- module Solutions.OAIFAE.AlgebraPresentations
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.bigAlgebra_countable _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.columnSpace_countable _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.freeAlgebra_finitelyPresented _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.polynomial_finitelyPresented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentations of tensor, opposite, contracted, unitized, and coefficient algebras.
-/

namespace FiniteAlgebraicEnvelopes.TensorPresentation
open scoped TensorProduct
variable (k : Type*) [CommRing k] (A C : Type*)

variable {A C}
variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop) (s : FreeAlgebra k C → FreeAlgebra k C → Prop)

theorem rel_finite [Finite A] [Finite C]
    (hr : {p : FreeAlgebra k A × FreeAlgebra k A | r p.1 p.2}.Finite)
    (hs : {p : FreeAlgebra k C × FreeAlgebra k C | s p.1 p.2}.Finite) :
    {p : F k A C × F k A C | Rel k r s p.1 p.2}.Finite := by
  let L := (fun p => (inLeft k A C p.1,inLeft k A C p.2)) '' {p : FreeAlgebra k A × FreeAlgebra k A | r p.1 p.2}
  let R := (fun p => (inRight k A C p.1,inRight k A C p.2)) '' {p : FreeAlgebra k C × FreeAlgebra k C | s p.1 p.2}
  let T := Set.range (fun p : A×C => (FreeAlgebra.ι k (Sum.inl p.1)*FreeAlgebra.ι k (Sum.inr p.2),
    FreeAlgebra.ι k (Sum.inr p.2)*FreeAlgebra.ι k (Sum.inl p.1)))
  apply (((hr.image _).union (hs.image _)).union (Set.finite_range _)).subset (s:= L ∪ R ∪ T)
  rintro ⟨a,b⟩ hp
  cases hp with
  | left hab => exact Or.inl (Or.inl ⟨(_, _),hab,rfl⟩)
  | right hab => exact Or.inl (Or.inr ⟨(_, _),hab,rfl⟩)
  | commute a c => exact Or.inr ⟨(a,c),rfl⟩

end FiniteAlgebraicEnvelopes.TensorPresentation

namespace FiniteAlgebraicEnvelopes.OppositePresentation
open MulOpposite
variable (k : Type*) [CommRing k] (A : Type*)

variable {A}
variable {R : Type*} [Ring R] [Algebra k R] (r : R → R → Prop)

omit [Ring R] [Algebra k R] in
theorem opRel_finite (hr : {p : R×R | r p.1 p.2}.Finite) :
    {p : Rᵐᵒᵖ×Rᵐᵒᵖ | opRel r p.1 p.2}.Finite := by
  apply (hr.image (fun p => (op p.1,op p.2))).subset
  rintro ⟨a,b⟩ h
  exact ⟨(a.unop,b.unop),h,rfl⟩

variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop)

theorem freeRel_finite (hr : {p : FreeAlgebra k A×FreeAlgebra k A | r p.1 p.2}.Finite) :
    {p : FreeAlgebra k A×FreeAlgebra k A | freeRel k r p.1 p.2}.Finite := by
  apply ((opRel_finite r hr).image (fun p => ((freeEquivalence k A).symm p.1,(freeEquivalence k A).symm p.2))).subset
  rintro ⟨a,b⟩ h
  refine ⟨((freeEquivalence k A) a,(freeEquivalence k A) b),h,?_⟩
  simp

end FiniteAlgebraicEnvelopes.OppositePresentation

namespace FiniteAlgebraicEnvelopes.AlgebraGenerators

section
open scoped TensorProduct
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

theorem tensorGenerators_finite {S : Set A} {T : Set B} (hS : S.Finite) (hT : T.Finite) :
    (tensorGenerators (k:=k) S T).Finite := (hS.image _).union (hT.image _)

theorem tensorGenerators_generate {S : Set A} {T : Set B}
    (hS : Algebra.adjoin k S=⊤) (hT : Algebra.adjoin k T=⊤) :
    Algebra.adjoin k (tensorGenerators (k:=k) S T)=⊤ := by
  let C := Algebra.adjoin k (tensorGenerators (k:=k) S T)
  have hl : ∀ a : A, Algebra.TensorProduct.includeLeft (R:=k) (S:=k) (A:=A) (B:=B) a∈C := by
    have hp : Algebra.adjoin k S≤C.comap (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) :=
      Algebra.adjoin_le (fun a ha => Algebra.subset_adjoin (Or.inl ⟨a,ha,rfl⟩))
    rw [hS] at hp
    intro a
    exact hp (by trivial)
  have hr : ∀ b : B, Algebra.TensorProduct.includeRight (R:=k) (A:=A) (B:=B) b∈C := by
    have hp : Algebra.adjoin k T≤C.comap (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) :=
      Algebra.adjoin_le (fun b hb => Algebra.subset_adjoin (Or.inr ⟨b,hb,rfl⟩))
    rw [hT] at hp
    intro b
    exact hp (by trivial)
  apply top_unique
  intro x _
  change x∈C
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have he : a⊗ₜ[k] b=(Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) a*(Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) b := by
      change a⊗ₜ[k] b=(a⊗ₜ[k] (1:B))*((1:A)⊗ₜ[k] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
    rw [he]
    exact C.mul_mem (hl a) (hr b)
  | add a b ha hb => exact C.add_mem (ha (by trivial)) (hb (by trivial))

theorem oppositeGenerators_generate {S : Set A} (hS : Algebra.adjoin k S=⊤) :
    Algebra.adjoin k (MulOpposite.op '' S)=⊤ := by
  have hset : MulOpposite.op '' S=MulOpposite.unop ⁻¹' S := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩; exact hb
    · intro ha; exact ⟨a.unop,ha,MulOpposite.op_unop a⟩
  rw [hset,←Subalgebra.op_adjoin,hS]
  exact Subalgebra.op_top

end

open scoped TensorProduct
variable {B : Type*} [Ring B] [Algebra (ZMod 2) B]

theorem envelopingGenerators_finite {S : Set B} (hS : S.Finite) :
    (envelopingGenerators S).Finite := tensorGenerators_finite hS (hS.image _)

theorem envelopingGenerators_generate {S : Set B} (hS : Algebra.adjoin (ZMod 2) S=⊤) :
    Subring.closure (envelopingGenerators S)=⊤ :=
  Steinberg.ringGenerators_of_algebraGenerators (R:=Enveloping.Coeff (ZMod 2) B)
    (tensorGenerators_generate (k:=ZMod 2) hS (oppositeGenerators_generate (k:=ZMod 2) hS))

end FiniteAlgebraicEnvelopes.AlgebraGenerators

section
namespace FiniteAlgebraicEnvelopes.ContractedPresentation
variable {k M : Type*} [CommRing k] [Nontrivial k] [MonoidWithZero M]

theorem monoidBasis_injective_nonzero {x y : M} (hx : x≠0)
    (he : monoidBasis k x=monoidBasis k y) : x=y := by
  classical
  have hh := congrArg (Contracted.coefficient (k:=k) x hx) he
  change Contracted.coefficient x hx (Contracted.basis k M x 1)=Contracted.coefficient x hx (Contracted.basis k M y 1) at hh
  rw [Contracted.coefficient_basis,Contracted.coefficient_basis] at hh
  by_contra hn
  simp [hn] at hh
end FiniteAlgebraicEnvelopes.ContractedPresentation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]
variable (hs : Subgroup.closure (Set.range s)=⊤)

theorem groupAlgebraEmbedding_injective : Function.Injective (groupAlgebraEmbedding s h k hs) := by
  intro x y he
  apply groupEmbedding_injective s h hs
  exact ContractedPresentation.monoidBasis_injective_nonzero
    (Units.ne_zero (groupUnitsEmbedding s h hs x)) he

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Unitize
variable {A B G : Type*} [Ring A] [Ring B] [Group G]
variable (i : A →ₙ+* B) (f : G →* A)

theorem hom_injective (hi : Function.Injective i) (hf : Function.Injective f) : Function.Injective (hom i f) := by
  intro x y he
  exact hf (hi (add_left_cancel he))

theorem unitsHom_injective (hi : Function.Injective i) (hf : Function.Injective f) : Function.Injective (unitsHom i f) := by
  intro x y he
  exact hom_injective i f hi hf (congrArg Units.val he)

end FiniteAlgebraicEnvelopes.Unitize

namespace FiniteAlgebraicEnvelopes.Enveloping
open scoped TensorProduct
variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

theorem eval_includeLeft (a : A) : eval k A (includeLeft k A a)=a := by
  rw [includeLeft_apply,←MulOpposite.op_one,eval_tmul,mul_one]

theorem includeLeft_injective : Function.Injective (includeLeft k A) :=
  Function.LeftInverse.injective (eval_includeLeft k A)

theorem unitsInclude_injective : Function.Injective (unitsInclude k A) := by
  intro x y he
  apply Units.ext
  exact includeLeft_injective k A (congrArg Units.val he)

end FiniteAlgebraicEnvelopes.Enveloping

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]
variable (hs : Subgroup.closure (Set.range s)=⊤)

theorem ambientUnits_injective : Function.Injective (ambientUnits s h k hs) :=
  Unitize.unitsHom_injective _ _ (algebraEmbedding_injective s h k) (groupAlgebraEmbedding_injective s h k hs)

theorem coefficientUnits_injective : Function.Injective (coefficientUnits s h k hs) :=
  (Enveloping.unitsInclude_injective k (BigAlgebra s h k)).comp (ambientUnits_injective s h k hs)

end

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]

theorem ringPsi_injective : Function.Injective (ringPsi s h k) := psi_injective s h k

theorem linearTransition_injective : Function.Injective (linearTransition s h k) :=
  Steinberg.elementaryTransition_injective (R:=R s h k) _ (ringPsi_injective s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

theorem ringGenerators_finite : (ringGenerators s h).Finite :=
  AlgebraGenerators.tensorGenerators_finite (bigGenerators_finite s h (ZMod 2))
    ((bigGenerators_finite s h (ZMod 2)).image _)

attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.ringRightSMul
theorem ringGenerators_generate : Subring.closure (ringGenerators s h) = ⊤ :=
  AlgebraGenerators.envelopingGenerators_generate (bigGenerators_generate s h (ZMod 2))

instance steinberg_finitelyGenerated : Group.FG (Steinberg.Group (Fin 6) (R s h (ZMod 2))) :=
  Steinberg.finitelyGenerated_of_ringGenerators (ringGenerators_finite s h) (ringGenerators_generate s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.EnvelopingPresentation
open scoped TensorProduct
variable (k : Type*) [CommRing k] {A : Type*}
variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop)

theorem rel_finite [Finite A]
    (hr : {p : FreeAlgebra k A × FreeAlgebra k A | r p.1 p.2}.Finite) :
    {p : FreeAlgebra k (Generators (A:=A)) × FreeAlgebra k (Generators (A:=A)) |
      Rel k r p.1 p.2}.Finite :=
  TensorPresentation.rel_finite k r (OppositePresentation.freeRel k r) hr
    (OppositePresentation.freeRel_finite k r hr)

end FiniteAlgebraicEnvelopes.EnvelopingPresentation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

theorem coefficientRelations_finite :
    {pair : FreeAlgebra k (CoefficientGenerators s h) × FreeAlgebra k (CoefficientGenerators s h) |
      CoefficientRelations s h k pair.1 pair.2}.Finite :=
  EnvelopingPresentation.rel_finite k (AlgebraRelations s h k) (algebraRelations_finite s h k)

/-- Finite-presentation reduction to the finite free algebra case. -/

theorem steinberg_finitePresentation_of_free
    [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (FreeAlgebra k (CoefficientGenerators s h)))] :
    Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (R s h k)) := by
  let : Group.IsFinitelyPresented (Steinberg.Group (Fin 6)
      (RingQuot (EnvelopingPresentation.Rel k (AlgebraRelations s h k)))) :=
    Steinberg.ringQuot_finitelyPresented (CoefficientRelations s h k) (coefficientRelations_finite s h k)
  exact Group.IsFinitelyPresented.equiv (Steinberg.coefficientEquiv (coefficientPresentation s h k).toRingEquiv)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
end

section
-- module Solutions.OAIFAE.AffineModules
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.SequentialLimit.torus_finitelyGenerated _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.freeAlgebra_finitelyPresented _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.polynomial_finitelyPresented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Affine module presentations, stabilized actions, and finite stabilizers.
-/

namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

/-- A detector after the coefficient map detects every entry of a matrix difference. -/
theorem correctedMatrix_eq_one (ψ : R →ₙ+* R) (b : V)
    (hb : ∀ r : R, ψ r • b=0 → r=0) (A : Matrix ι ι R)
    (hA : ∀ j : ι, applyMatrix (correctedMap (matrixNonunitalMap ψ) A)
      (Pi.single j b)=Pi.single j b) : A=1 := by
  have he (j : ι) : applyMatrix (matrixNonunitalMap ψ (A-1)) (Pi.single j b)=0 := by
    have hh := hA j
    change applyMatrix (1+matrixNonunitalMap ψ (A-1)) (Pi.single j b)=Pi.single j b at hh
    rw [applyMatrix_add,applyMatrix_one] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  apply sub_eq_zero.mp
  ext i j
  apply hb
  simpa using congrFun (he j) i

/-- In particular a corrected unit acting trivially on all columns was already the identity. -/
theorem correctedUnits_eq_one (ψ : R →ₙ+* R) (b : V)
    (hb : ∀ r : R, ψ r • b=0 → r=0) (A : (Matrix (Fin 6) (Fin 6) R)ˣ)
    (hA : ∀ v : Multiplicative (Fin 6 → V), unitsAction (Steinberg.correctedUnits ψ A) v=v) : A=1 := by
  apply Units.ext
  apply correctedMatrix_eq_one ψ b hb
  intro j
  exact congrArg Multiplicative.toAdd (hA (Multiplicative.ofAdd (Pi.single j b)))

end FiniteAlgebraicEnvelopes.MatrixModule

section
namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

theorem stage_mono {i j : ℕ} (hij : i≤j) : stage f i ⊆ stage f j := by
  rintro _ ⟨x,rfl⟩
  exact ⟨transition f i j hij x,of_transition f i j hij x⟩

theorem next_marker_not_mem (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) (j : ℕ) :
    of f (j+1) w∉stage f j := by
  rintro ⟨x,hx⟩
  apply hw
  refine ⟨x,of_injective f hf (j+1) ?_⟩
  exact (of_succ f j x).trans hx

theorem marker_ne (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) {i j : ℕ} (hij : i<j) :
    of f i w≠of f j w := by
  intro he
  have ht : transition f i j (Nat.le_of_lt hij) w=w :=
    of_injective f hf j ((of_transition f i j (Nat.le_of_lt hij) w).trans he)
  have hn : j-i=(j-i-1)+1 := by omega
  change (f^(j-i)) w=w at ht
  rw [hn,pow_succ'] at ht
  exact hw ⟨(f^(j-i-1)) w,ht⟩

theorem markers_injective (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) :
    Function.Injective (fun j : ℕ => of f j w) := by
  intro i j he
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij|hji
  · exact marker_ne f hf hw hij he
  · exact marker_ne f hf hw hji he.symm

theorem infinite_of_marker (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) : Infinite (Limit f) :=
  Infinite.of_injective _ (markers_injective f hf hw)

end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.ColumnLimit
variable {B : Type*} [Ring B] (φ : B →ₙ+* B)

theorem transition_injective (hφ : Function.Injective φ) : Function.Injective (transition φ) := by
  intro x y he
  apply Multiplicative.toAdd.injective
  funext i
  exact hφ (congrArg (fun v : Multiplicative (Fin 6 → B) => v.toAdd i) he)

theorem one_not_range (hφ1 : φ 1≠1) : (1:B)∉Set.range φ := by
  rintro ⟨x,hx⟩
  apply hφ1
  have he : φ 1*φ x=φ x := by rw [←map_mul,one_mul]
  rwa [hx,mul_one] at he

theorem marker_not_range (hφ1 : φ 1≠1) : marker (B:=B)∉Set.range (transition φ) := by
  rintro ⟨x,hx⟩
  apply one_not_range φ hφ1
  refine ⟨x.toAdd 0,?_⟩
  exact congrArg (fun v : Multiplicative (Fin 6 → B) => v.toAdd 0) hx

theorem limit_infinite (hφ : Function.Injective φ) (hφ1 : φ 1≠1) :
    Infinite (SequentialLimit.Limit (transition φ)) :=
  SequentialLimit.infinite_of_marker _ (transition_injective φ hφ) (marker_not_range φ hφ1)

end FiniteAlgebraicEnvelopes.ColumnLimit
end

section

namespace FiniteAlgebraicEnvelopes.LimitAction
open SequentialLimit
variable {Q V : Type*} [Group Q] [Group V]
variable (α : Q →* MulAut V) (f : Monoid.End Q) (g : Monoid.End V)
variable (hc : ∀ x v, g (α x v)=α (f x) (g v))

include hc

/-- Detection after one transition suffices for faithfulness on the direct limit. -/
theorem action_injective (hg : Function.Injective g)
    (hd : ∀ x : Q, (∀ v : V, α (f x) v=v) → x=1) : Function.Injective (action α f g hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x=1
  change action α f g hc x=1 at hx
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition f) x
  change action α f g hc (of f i x)=1 at hx
  change of f i x=1
  have hx1 : x=1 := hd x (by
    intro v
    have he := DFunLike.congr_fun hx (of g (i+1) v)
    rw [←of_succ f i x,action_of] at he
    exact of_injective g hg (i+1) he)
  rw [hx1,map_one]

end FiniteAlgebraicEnvelopes.LimitAction
end

section

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open SequentialLimit
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (φ : B →ₙₐ[k] B)

theorem limitAction_injective (hφ : Function.Injective φ) (b : B)
    (hd : ∀ r : Enveloping.Coeff k B, Enveloping.act k B (coefficientRing φ r) b=0 → r=0) :
    Function.Injective (limitAction φ) := by
  apply LimitAction.action_injective _ _ _ _ (ColumnLimit.transition_injective _ hφ)
  intro x hx
  apply Subtype.ext
  exact MatrixModule.correctedUnits_eq_one (coefficientRing φ) b hd x.val hx

end FiniteAlgebraicEnvelopes.NonunitalTensor
end

namespace FiniteAlgebraicEnvelopes.Enveloping
variable {B : Type*} [Ring B] [Algebra (ZMod 2) B]

/-- The manuscript cyclic-module and finite relative-presentation lemmas assembled.
The Steinberg finite-presentation premise is precisely the separate cited theorem. -/
theorem affine_finitePresentation (S : Set B) (hS : S.Finite) (hgen : Algebra.adjoin (ZMod 2) S=⊤)
    [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (Coeff (ZMod 2) B))] :
    Group.IsFinitelyPresented (AffineAction.Group (R:=Coeff (ZMod 2) B) (V:=B)) := by
  classical
  let T := AlgebraGenerators.envelopingGenerators S
  have hT : T.Finite := AlgebraGenerators.envelopingGenerators_finite hS
  let F : Finset (Coeff (ZMod 2) B) := insert 1 hT.toFinset
  have hF1 : (1 : Coeff (ZMod 2) B) ∈ F := Finset.mem_insert_self _ _
  have hF : Subring.closure (↑F : Set (Coeff (ZMod 2) B))=⊤ := by
    apply top_unique
    rw [←AlgebraGenerators.envelopingGenerators_generate hgen]
    apply Subring.closure_mono
    intro x hx
    exact Finset.mem_insert_of_mem (by simpa using hx)
  have hD := hS.image (difference (ZMod 2) B)
  let D := hD.toFinset
  have hDset : (↑D : Set (Coeff (ZMod 2) B))=difference (ZMod 2) B '' S := hD.coe_toFinset
  have hDrel : Submodule.span (Coeff (ZMod 2) B) (↑D : Set (Coeff (ZMod 2) B))=relations (k:=ZMod 2) S := by
    rw [hDset]
    rfl
  let := FiniteAffine.affine_finitelyPresented F D hF1 hF
  let e : (Coeff (ZMod 2) B ⧸ Submodule.span (Coeff (ZMod 2) B) (↑D : Set (Coeff (ZMod 2) B))) ≃ₗ[Coeff (ZMod 2) B] B :=
    (Submodule.quotEquivOfEq _ _ hDrel).trans (quotientEquiv S hgen)
  exact Group.IsFinitelyPresented.equiv (MatrixModule.affineEquiv e)

end FiniteAlgebraicEnvelopes.Enveloping

namespace FiniteAlgebraicEnvelopes.LimitAction
open SequentialLimit
variable {Q V : Type*} [Group Q] [Group V]
variable (α : Q →* MulAut V) (f : Monoid.End Q) (g : Monoid.End V)
variable (hc : ∀ x v, g (α x v)=α (f x) (g v))

/-- One step into the simple-algebra image gives transitivity in the limit. -/
theorem transitive_nonone
    (ht : ∀ v w : V, v≠1 → w≠1 → ∃ x : Q, α x (g v)=g w)
    (v w : Limit g) (hv : v≠1) (hw : w≠1) :
    ∃ x : Limit f, action α f g hc x v=w := by
  obtain ⟨i,v,w,rfl,rfl⟩ := exists_common_stage₂ g g v w
  have hv1 : v≠1 := by intro he; exact hv (he ▸ map_one _)
  have hw1 : w≠1 := by intro he; exact hw (he ▸ map_one _)
  obtain ⟨x,hx⟩ := ht v w hv1 hw1
  refine ⟨of f (i+1) x,?_⟩
  rw [←of_succ g i v,action_of,hx,of_succ]

/-- A finite-stage linear element cannot be a strictly advancing shift. -/
theorem ne_positive_shift (hg : Function.Injective g) {w : V} (hw : w∉Set.range g)
    (x : Limit f) (n : ℕ) (hn : 0<n) : action α f g hc x≠(shift g)^n := by
  obtain ⟨i,q,rfl⟩ := DirectLimit.exists_eq_mk (transition f) x
  intro he
  have hv := DFunLike.congr_fun he (of g i w)
  change action α f g hc (of f i q) (of g i w)=((shift g)^n) (of g i w) at hv
  rw [action_of,shift_pow_of] at hv
  have hm : of g (i+n) w∈stage g i := ⟨α q w,hv⟩
  have hm' := stage_mono g (show i ≤ i + n - 1 from by omega) hm
  have heq : i+n=(i+n-1)+1 := by omega
  rw [heq] at hm'
  exact next_marker_not_mem g hg hw (i+n-1) hm'

theorem shift_exponent_zero (hg : Function.Injective g) {w : V} (hw : w∉Set.range g)
    (x : Limit f) (z : ℤ) (he : action α f g hc x=(shift g)^z) : z=0 := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      exact False.elim (ne_positive_shift α f g hc hg hw x (n+1) (Nat.succ_pos _) (by
        change action α f g hc x=(shift g)^((n+1 : ℕ):ℤ) at he
        rwa [zpow_natCast] at he))
  | negSucc n =>
    have hi := congrArg Inv.inv he
    have hi' : action α f g hc x⁻¹=(shift g)^(n+1) := by
      simpa only [←map_inv,zpow_negSucc,inv_inv] using hi
    exact False.elim (ne_positive_shift α f g hc hg hw x⁻¹ (n+1) (Nat.succ_pos _) hi')

theorem torusAction_injective (hα : Function.Injective (action α f g hc))
    (hg : Function.Injective g) {w : V} (hw : w∉Set.range g) :
    Function.Injective (torusAction α f g hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro a ha
  change a=1
  have he : action α f g hc a.left * (shift g)^a.right.toAdd=1 := ha
  have hz : a.right.toAdd=0 := shift_exponent_zero α f g hc hg hw a.left⁻¹ a.right.toAdd (by
    rw [map_inv]
    exact (inv_eq_of_mul_eq_one_right he))
  have hr : a.right=1 := Multiplicative.toAdd.injective hz
  have hl : a.left=1 := hα (by simpa [hz] using he)
  exact SemidirectProduct.ext hl hr

end FiniteAlgebraicEnvelopes.LimitAction

end

end OAI
end

section
-- module Solutions.OAIFAE.GroupInput
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.bigAlgebra_countable _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.columnSpace_countable _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.hFG _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.hMonoidWithZero _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.hNontrivial _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.kFG _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.kMonoidWithZero _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.kNontrivial _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.steinberg_finitelyGenerated _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Wreath-product reduction to countably infinite finitely generated decidable input groups.
-/


namespace FiniteAlgebraicEnvelopes
universe u
namespace GroupInput
variable (G : Type u) [Group G]

theorem embed_injective : Function.Injective (embed G) := by
  intro a b h
  have hh := congrArg SemidirectProduct.left h
  have h0 := congrFun hh 0
  have h1 := congrFun hh 1
  exact Prod.ext (by simpa [embed, base] using h0) (by simpa [embed, base] using h1)

theorem stable_conj (g : G) :
    stable G * embed G (g,g) * (stable G)⁻¹ = embed G (1,g) := by
  simp only [stable, embed, MonoidHom.comp_apply, ← map_inv, ← SemidirectProduct.inl_aut]
  apply congrArg SemidirectProduct.inl
  ext i
  change (if i - 1 < 0 then 1 else if i - 1 = 0 then g else g) =
    (if i < 0 then 1 else if i = 0 then 1 else g)
  split_ifs <;> first | rfl | omega

theorem commutator (g : G) :
    embed G (g,g) * stable G * (embed G (g,g))⁻¹ * (stable G)⁻¹ = embed G (g,1) := by
  rw [mul_assoc (embed G (g,g)), mul_assoc (embed G (g,g)),
    ← map_inv, Prod.inv_mk, stable_conj G g⁻¹, ← map_mul]
  simp

theorem value_right {n} (s : Fin n → G) (w : InputWord n) :
    (value G s w).right.toAdd = height w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [value_cons, SemidirectProduct.mul_right]
    change (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).right.toAdd +
      (value G s w).right.toAdd = heightLetter a + height w
    rw [ih]
    congr 1
    rcases a with ⟨_ | ⟨i,b⟩,t⟩ <;> cases t
    all_goals try cases b
    all_goals simp [generators, stable, embed, heightLetter]

theorem signed_right {n} (s : Fin n → G) (a : Letters n × Bool) :
    (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).right =
      Multiplicative.ofAdd (heightLetter a) := by
  rcases a with ⟨_ | ⟨j,b⟩,t⟩ <;> cases t
  all_goals try cases b
  all_goals rfl

theorem signed_left {n} (s : Fin n → G) (a : Letters n × Bool) (i : ℤ) :
    (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).left i =
      evalWord s (atLetter a i) := by
  rcases a with ⟨_ | ⟨j,b⟩,t⟩ <;> cases t
  · change (1 : G)⁻¹ = 1
    exact inv_one
  · rfl
  all_goals cases b
  all_goals simp only [generators, Bool.false_eq_true, ↓reduceIte, embed,
    MonoidHom.comp_apply, ← map_inv, SemidirectProduct.left_inl, base,
    MonoidHom.coe_mk, OneHom.coe_mk,
    atLetter, evalWord]
  all_goals split_ifs <;> simp_all [List.map_cons, List.prod_cons] <;> try omega
  all_goals split_ifs <;> first | rfl | omega

theorem value_cons_left {n} (s : Fin n → G) (a : Letters n × Bool)
    (w : InputWord n) (i : ℤ) :
    (value G s (a::w)).left i = evalWord s (atLetter a i) *
      (value G s w).left (i - heightLetter a) := by
  rw [value_cons, SemidirectProduct.mul_left]
  change (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).left i *
    (value G s w).left (i - (if a.2 then generators G s a.1 else
      (generators G s a.1)⁻¹).right.toAdd) = _
  rw [signed_left, signed_right]
  rfl

theorem value_left {n} (s : Fin n → G) (w : InputWord n) (i : ℤ) :
    (value G s w).left i = evalWord s (sectionWord i w) := by
  induction w generalizing i with
  | nil => rfl
  | cons a w ih =>
    rw [value_cons_left, ih]
    simp [sectionWord, evalWord, List.map_append, List.prod_append]

theorem at_low {n} (w : InputWord n) (i : ℤ) (hi : i < -(w.length : ℤ)) :
    sectionWord i w = [] := by
  induction w generalizing i with
  | nil => rfl
  | cons a w ih =>
    have hb := heightLetter_bounds a
    have hil : i < 0 := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi; omega
    have hii : i - heightLetter a < -(w.length : ℤ) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi; omega
    rw [sectionWord, ih _ hii]
    simp only [List.append_nil]
    rcases a with ⟨_ | ⟨j,b⟩,t⟩ <;> simp [atLetter, ne_of_lt hil, not_lt_of_ge (le_of_lt hil)]

theorem at_high {n} (w : InputWord n) (i j : ℤ)
    (hi : (w.length : ℤ) < i) (hj : (w.length : ℤ) < j) : sectionWord i w = sectionWord j w := by
  induction w generalizing i j with
  | nil => rfl
  | cons a w ih =>
    have hb := heightLetter_bounds a
    have his : 0 < i ∧ (w.length : ℤ) < i - heightLetter a := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi; omega
    have hjs : 0 < j ∧ (w.length : ℤ) < j - heightLetter a := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hj; omega
    rw [sectionWord, sectionWord, ih _ _ his.2 hjs.2]
    congr 1
    rcases a with ⟨_ | ⟨k,b⟩,t⟩ <;>
      simp [atLetter, ne_of_gt his.1, ne_of_gt hjs.1, his.1, hjs.1]

theorem value_eq_one_iff {n} (s : Fin n → G) (w : InputWord n) :
    value G s w = 1 ↔ height w = 0 ∧
      ∀ k ∈ List.range (2 * w.length + 3),
        evalWord s (sectionWord ((k : ℤ) - (w.length : ℤ) - 1) w) = 1 := by
  constructor
  · intro h
    constructor
    · rw [← value_right G s, h]; rfl
    · intro k _; rw [← value_left G s, h]; rfl
  · rintro ⟨hh, hv⟩
    apply SemidirectProduct.ext
    · funext i
      change (value G s w).left i = 1
      rw [value_left]
      by_cases hi : i < -(w.length : ℤ)
      · rw [at_low w i hi]; rfl
      by_cases hj : (w.length : ℤ) + 1 < i
      · have hk := hv (2*w.length+2) (List.mem_range.mpr (by omega))
        have he : ((2*w.length+2 : ℕ) : ℤ) - (w.length : ℤ) - 1 =
            (w.length : ℤ) + 1 := by push_cast; omega
        rw [he] at hk
        rw [at_high w i ((w.length : ℤ)+1) (by omega) (by omega)]
        exact hk
      · let k := (i + (w.length : ℤ) + 1).toNat
        have hk : (k : ℤ) = i + (w.length : ℤ) + 1 := Int.toNat_of_nonneg (by omega)
        have hkr : k < 2*w.length+3 := by omega
        have hki : (k : ℤ) - (w.length : ℤ) - 1 = i := by omega
        simpa only [hki] using hv k (List.mem_range.mpr hkr)
    · apply Multiplicative.toAdd.injective
      exact (value_right G s w).trans hh

theorem heightLetter_eq {n} (a : Letters n × Bool) :
    heightLetter a = ((countsLetter a).1 : ℤ) - ((countsLetter a).2 : ℤ) := by
  rcases a with ⟨_ | ⟨j,b⟩,t⟩ <;> cases t <;> rfl

theorem counts_fold {n} (w : InputWord n) (p q : ℕ) :
    let c := w.foldl (fun c a => (c.1 + (countsLetter a).1, c.2 + (countsLetter a).2)) (p,q)
    (c.1 : ℤ) - (c.2 : ℤ) = (p : ℤ) - (q : ℤ) + height w := by
  induction w generalizing p q with
  | nil => simp
  | cons a w ih =>
    simp only [List.foldl_cons, height_cons]
    rw [ih, heightLetter_eq]
    push_cast
    ring

theorem counts_eq_height {n} (w : InputWord n) :
    ((counts w).1 : ℤ) - ((counts w).2 : ℤ) = height w := by
  simpa [counts] using counts_fold w 0 0

theorem natAtLetter_eq {n} (a : Letters n × Bool) (p q : ℕ) :
    natAtLetter a (p,q) = atLetter a ((p : ℤ) - (q : ℤ)) := by
  rcases a with ⟨_ | ⟨j,b⟩,t⟩
  · rfl
  · simp [natAtLetter, atLetter, sub_eq_zero]

theorem natStep_fold {n} (w : InputWord n) (p q : ℕ) (v : Word n) :
    (w.foldl natStep ((p,q),v)).2 = v ++ sectionWord ((p : ℤ) - (q : ℤ)) w := by
  induction w generalizing p q v with
  | nil => simp [sectionWord]
  | cons a w ih =>
    simp only [List.foldl_cons, natStep]
    rw [ih, natAtLetter_eq, List.append_assoc]
    simp only [sectionWord]
    congr 2
    rw [heightLetter_eq]
    push_cast
    congr 1
    ring

theorem natAt_eq {n} (w : InputWord n) (p q : ℕ) :
    natAt w (p,q) = sectionWord ((p : ℤ) - (q : ℤ)) w := by
  simpa [natAt] using natStep_fold w p q []

open Primrec

theorem countsLetter_primrec (n) : Primrec (@countsLetter n) := Primrec.dom_finite _

theorem counts_primrec (n) : Primrec (@counts n) := by
  unfold counts
  apply Primrec.list_foldl (h := fun _ ca =>
    (ca.1.1 + (countsLetter ca.2).1, ca.1.2 + (countsLetter ca.2).2))
    Primrec.id (Primrec.const (0,0))
  unfold Primrec₂
  apply Primrec.pair
  · exact Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp ((countsLetter_primrec n).comp (Primrec.snd.comp Primrec.snd)))
  · exact Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp ((countsLetter_primrec n).comp (Primrec.snd.comp Primrec.snd)))

theorem natAtLetter_primrec (n) : Primrec₂ (@natAtLetter n) := by
  unfold natAtLetter Primrec₂
  refine (Primrec.option_casesOn (g := fun a jb =>
    if (jb.2 = false ∧ a.2.1 = a.2.2) ∨ (jb.2 = true ∧ a.2.2 < a.2.1)
    then [(jb.1,a.1.2)] else [])
    (Primrec.fst.comp Primrec.fst) (Primrec.const []) ?_).of_eq (fun a => by
      rcases a with ⟨⟨_ | ⟨j,b⟩,t⟩,pq⟩ <;> rfl)
  unfold Primrec₂
  apply Primrec.ite
  · exact ((Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const false)).and
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).or
      ((Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true)).and
      (Primrec.nat_lt.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  · exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const [])
  · exact Primrec.const []

theorem natStep_primrec (n) : Primrec₂ (@natStep n) := by
  unfold natStep Primrec₂
  apply Primrec.pair
  · exact Primrec.pair
      (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp ((countsLetter_primrec n).comp Primrec.snd)))
      (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp ((countsLetter_primrec n).comp Primrec.snd)))
  · exact Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      ((natAtLetter_primrec n).comp Primrec.snd (Primrec.fst.comp Primrec.fst))

theorem natAt_primrec (n) : Primrec₂ (@natAt n) := by
  unfold natAt Primrec₂
  apply Primrec.snd.comp
  exact Primrec.list_foldl Primrec.fst (Primrec.pair Primrec.snd (Primrec.const []))
    (((natStep_primrec n).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)

/-- Closure of genuine computability under a variable finite universal test. -/
theorem computable_forall_lt {α : Type*} [Primcodable α] {p : α × ℕ → Prop}
    (hp : ComputablePred p) : ComputablePred (fun a : α × ℕ => ∀ k < a.2, p (a.1,k)) := by
  classical
  let test (a : α) : ℕ → Bool := Nat.rec true (fun k b => b && decide (p (a,k)))
  have hc : Computable₂ test := by
    unfold test Computable₂
    apply Computable.nat_rec (h := fun a kb => kb.2 && decide (p (a.1,kb.1)))
      Computable.snd (Computable.const true)
    exact ((Primrec.and.to_comp).comp (Computable.snd.comp Computable.snd)
      (hp.decide.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)))).to₂
  have ht (a : α) (n : ℕ) : test a n = true ↔ ∀ k < n, p (a,k) := by
    induction n with
    | zero => simp [test]
    | succ n ih =>
      change (test a n && decide (p (a,n))) = true ↔ _
      simp only [Bool.and_eq_true, decide_eq_true_eq, ih]
      exact ⟨fun h k hk => (Nat.lt_succ_iff_lt_or_eq.mp hk).elim (h.1 k) (fun he => he ▸ h.2),
        fun h => ⟨fun k hk => h k (by omega),h n (by omega)⟩⟩
  have hh : ComputablePred (fun a : α × ℕ => test a.1 a.2 = true) :=
    ⟨fun a => Classical.propDecidable (test a.1 a.2 = true),
      (show Computable (fun a : α × ℕ => test a.1 a.2) from hc).of_eq
        (fun a => by simp only [Bool.decide_eq_true])⟩
  exact hh.of_eq fun a => ht a.1 a.2

/-- The decision procedure for this finitely generated wreath subgroup. -/
theorem value_wordProblem {n} (s : Fin n → G)
    (hs : ComputablePred (fun w : Word n => evalWord s w = 1)) :
    ComputablePred (fun w : InputWord n => value G s w = 1) := by
  classical
  have hc : ComputablePred (fun w : InputWord n => (counts w).1 = (counts w).2) :=
    (Primrec.eq.comp (Primrec.fst.comp (counts_primrec n))
      (Primrec.snd.comp (counts_primrec n))).computablePred
  have hp : ComputablePred (fun a : InputWord n × ℕ =>
      evalWord s (natAt a.1 (a.2, a.1.length+1)) = 1) :=
    ⟨inferInstance, hs.decide.comp ((natAt_primrec n).comp Primrec.fst
      (Primrec.pair Primrec.snd (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)))).to_comp⟩
  have hq : ComputablePred (fun w : InputWord n =>
      ∀ k < 2*w.length+3, evalWord s (natAt w (k,w.length+1)) = 1) :=
    ⟨inferInstance, (computable_forall_lt hp).decide.comp
      (Primrec.pair Primrec.id (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.list_length) (Primrec.const 3))).to_comp⟩
  have ht : ComputablePred (fun w : InputWord n =>
      (counts w).1 = (counts w).2 ∧
      ∀ k < 2*w.length+3, evalWord s (natAt w (k,w.length+1)) = 1) :=
    ⟨inferInstance, by simpa only [Bool.decide_and] using
      ((Primrec.and.to_comp).comp hc.decide hq.decide)⟩
  exact ht.of_eq fun w => by
    rw [value_eq_one_iff]
    constructor
    · rintro ⟨h, hv⟩
      constructor
      · have hh := counts_eq_height w
        rw [h, sub_self] at hh
        exact hh.symm
      · intro k hk
        have hvk := hv k (List.mem_range.mp hk)
        simpa [natAt_eq, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hvk
    · rintro ⟨h, hv⟩
      constructor
      · have hh := counts_eq_height w
        rw [h, sub_eq_zero] at hh
        exact Int.ofNat_inj.mp hh
      · intro k hk
        simpa [natAt_eq, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hv k (List.mem_range.mpr hk)

theorem embed_mem_generated {n} (s : Fin n → G)
    (hs : Subgroup.closure (Set.range s) = ⊤) (a b : G) :
    embed G (a,b) ∈ generated G s := by
  have hl : ∀ x : G, embed G (x,1) ∈ generated G s := by
    have hle : Subgroup.closure (Set.range s) ≤ (generated G s).comap
        ((embed G).comp (MonoidHom.inl G G)) := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i,rfl⟩
      exact Subgroup.subset_closure ⟨some (i,false),rfl⟩
    rw [hs] at hle
    exact fun x => hle (Subgroup.mem_top x)
  have hr : ∀ x : G, embed G (1,x) ∈ generated G s := by
    have hle : Subgroup.closure (Set.range s) ≤ (generated G s).comap
        ((embed G).comp (MonoidHom.inr G G)) := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i,rfl⟩
      exact Subgroup.subset_closure ⟨some (i,true),rfl⟩
    rw [hs] at hle
    exact fun x => hle (Subgroup.mem_top x)
  have hh := (generated G s).mul_mem (hl a) (hr b)
  rwa [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] at hh

theorem subgroupGenerators_generate {n} (s : Fin n → G) :
    Subgroup.closure (Set.range (subgroupGenerators G s)) = ⊤ := by
  apply Subgroup.map_injective (generated G s).subtype_injective
  rw [MonoidHom.map_closure]
  have him : (generated G s).subtype '' Set.range (subgroupGenerators G s) =
      Set.range (generators G s) := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩; exact ⟨a,rfl⟩
    · rintro ⟨a,rfl⟩; exact ⟨subgroupGenerators G s a,⟨a,rfl⟩,rfl⟩
  rw [him]
  change generated G s = Subgroup.map (generated G s).subtype ⊤
  ext x
  constructor
  · intro hx; exact ⟨⟨x,hx⟩,Subgroup.mem_top _,rfl⟩
  · rintro ⟨y,_,rfl⟩; exact y.property

theorem generated_fg {n} (s : Fin n → G) : Group.FG (generated G s) :=
  Group.fg_iff.mpr ⟨Set.range (subgroupGenerators G s), subgroupGenerators_generate G s,
    Set.finite_range _⟩

theorem generated_wordProblem {n} (s : Fin n → G)
    (hs : ComputablePred (fun w : Word n => evalWord s w = 1)) :
    HasDecidableWordProblem (generated G s) := by
  classical
  let m := Fintype.card (Letters n)
  let e : Letters n ≃ Fin m := Fintype.equivFin (Letters n)
  let t : Fin m → generated G s := fun i => subgroupGenerators G s (e.symm i)
  have hgen : Set.range t = Set.range (subgroupGenerators G s) := by
    ext x
    exact ⟨fun ⟨i,hi⟩ => ⟨e.symm i,hi⟩, fun ⟨a,ha⟩ => ⟨e a,by simpa [t] using ha⟩⟩
  refine ⟨m,t,hgen ▸ subgroupGenerators_generate G s,?_⟩
  let tr (w : Word m) : InputWord n := w.map fun a => (e.symm a.1,a.2)
  have ht : Primrec tr :=
    Primrec.list_map Primrec.id ((Primrec.dom_finite (fun a : Fin m × Bool =>
      (e.symm a.1,a.2))).comp Primrec.snd)
  have hc : ComputablePred (fun w : Word m => value G s (tr w) = 1) :=
    ⟨inferInstance, (value_wordProblem G s hs).decide.comp ht.to_comp⟩
  exact hc.of_eq fun w => by
    have he : ((evalWord t w : generated G s) : Ambient G) = value G s (tr w) := by
      change (generated G s).subtype (evalWord t w) = _
      simp only [evalWord, tr, value, map_list_prod, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro a _
      cases a.2 <;> rfl
    rw [← he]
    change (generated G s).subtype (evalWord t w) = (generated G s).subtype 1 ↔ _
    exact (generated G s).subtype_injective.eq_iff

end GroupInput

/-- Wreath-product reduction using an explicit step-function witness.
The construction includes finite and trivial input groups. -/
theorem group_input (G : Type u) [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Group.FG H ∧ HasDecidableWordProblem H ∧
      ∃ (f : G × G →* H) (s : H), Function.Injective f ∧
        ∀ g : G, f (g,g) * s * (f (g,g))⁻¹ * s⁻¹ = f (g,1) := by
  obtain ⟨n,t,hgen,hwp⟩ := hG
  let H := GroupInput.generated G t
  let f : G × G →* H := (GroupInput.embed G).codRestrict H fun ab =>
    GroupInput.embed_mem_generated G t hgen ab.1 ab.2
  let s : H := ⟨GroupInput.stable G,Subgroup.subset_closure ⟨none,rfl⟩⟩
  refine ⟨H,inferInstance,GroupInput.generated_fg G t,
    GroupInput.generated_wordProblem G t hwp,f,s,?_,?_⟩
  · intro a b h
    exact GroupInput.embed_injective G (congrArg Subtype.val h)
  · intro g
    apply Subtype.val_injective
    exact GroupInput.commutator G g


end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.ActionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Full finitely presented faithful two-transitive action envelope and type-(A) applications.
-/

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

section
open SequentialLimit
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (φ : B →ₙₐ[k] B)

theorem torusAction_injective (hφ : Function.Injective φ) (hφ1 : φ 1≠1) (b : B)
    (hd : ∀ r : Enveloping.Coeff k B, Enveloping.act k B (coefficientRing φ r) b=0 → r=0) :
    Function.Injective (torusAction φ) :=
  LimitAction.torusAction_injective (linearAction (k:=k) (B:=B)) (linearStep φ) (columnStep φ)
    (linear_column_compatible φ) (limitAction_injective φ hφ b hd)
    (ColumnLimit.transition_injective _ hφ) (ColumnLimit.marker_not_range _ hφ1)

end

open SequentialLimit
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B] [IsSimpleRing A]
variable (i : A →ₙₐ[k] B) (j : B →ₙₐ[k] A) (hj : Function.Injective j)

include hj in
theorem columnStep_transitive (v w : Columns (B:=B)) (hv : v≠1) (hw : w≠1) :
    ∃ x : LinearGroup (k:=k) (B:=B), linearAction x (columnStep (i.comp j) v)=columnStep (i.comp j) w := by
  have hn (u : Columns (B:=B)) (hu : u≠1) : (fun c : Fin 6 => j (u.toAdd c))≠0 := by
    intro hz
    apply hu
    apply Multiplicative.toAdd.injective
    funext c
    apply hj
    exact (congrFun hz c).trans (map_zero j).symm
  obtain ⟨z,hz⟩ := RowControl.transitive_nonzero i (fun c => j (v.toAdd c)) (fun c => j (w.toAdd c))
    (hn v hv) (hn w hw)
  refine ⟨Steinberg.elementaryQuotient z,?_⟩
  change MatrixModule.elementaryAction (Steinberg.elementaryQuotient z) (columnStep (i.comp j) v)=columnStep (i.comp j) w
  rw [MatrixModule.elementaryAction_quotient]
  apply Multiplicative.toAdd.injective
  exact hz

include hj in
theorem limit_transitive :
    ∀ left right : Limit (columnStep (i.comp j)), left≠1 → right≠1 →
      ∃ actor : Limit (linearStep (i.comp j)), limitAction (i.comp j) actor left=right :=
  LimitAction.transitive_nonone (linearAction (k:=k) (B:=B)) (linearStep (i.comp j)) (columnStep (i.comp j))
    (linear_column_compatible (i.comp j)) (columnStep_transitive i j hj)

end FiniteAlgebraicEnvelopes.NonunitalTensor

section
namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

theorem columnSpace_infinite : Infinite (ColumnSpace s h) :=
  ColumnLimit.limit_infinite (B:=BigAlgebra s h (ZMod 2)) (phi s h (ZMod 2) : BigAlgebra s h (ZMod 2) →ₙ+* BigAlgebra s h (ZMod 2))
    (phi_injective s h (ZMod 2)) (phi_one_ne_one s h (ZMod 2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]

theorem fixed_tensor_detector (r : R s h k)
    (hr : Enveloping.act k (BigAlgebra s h k) (psi s h k r) (detectingElement s h k)=0) : r=0 := by
  apply detectionLinear_injective s h k
  rw [detectionLinear_apply,hr,LinearMap.map_zero]

end

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

theorem linear_transitive :
    ∀ left right : ColumnSpace s h, left≠1 → right≠1 →
      ∃ actor : SequentialLimit.Limit (NonunitalTensor.linearStep (phi s h (ZMod 2))),
        linearAction s h (ZMod 2) actor left=right :=
  letI := smallAlgebra_simple s h (ZMod 2)
  NonunitalTensor.limit_transitive (algebraEmbedding s h (ZMod 2)) (j s h (ZMod 2))
    (j_injective s h (ZMod 2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.AffinePermutation
variable {Q V : Type*} [Group Q] [Group V] (α : Q →* MulAut V)

theorem faithful (hα : Function.Injective α) : FaithfulSMul (V ⋊[α] Q) V where
  eq_of_smul_eq_smul := by
    intro a b hab
    have hl : a.left=b.left := by simpa using hab 1
    have hr : a.right=b.right := hα (by
      apply MulEquiv.ext
      intro v
      have he := hab v
      simp only [smul_apply,hl] at he
      exact mul_left_cancel he)
    exact SemidirectProduct.ext hl hr

/-- The ordinary affine formula upgrades linear nonzero transitivity to ordered-pair transitivity. -/
theorem two_transitive
    (ht : ∀ v w : V, v≠1 → w≠1 → ∃ x : Q, α x v=w)
    (x₁ x₂ y₁ y₂ : V) (hx : x₁≠x₂) (hy : y₁≠y₂) :
    ∃ a : V ⋊[α] Q, a • x₁=y₁ ∧ a • x₂=y₂ := by
  have hxx : x₁⁻¹*x₂≠1 := by intro h; exact hx (inv_mul_eq_one.mp h)
  have hyy : y₁⁻¹*y₂≠1 := by intro h; exact hy (inv_mul_eq_one.mp h)
  obtain ⟨q,hq⟩ := ht (x₁⁻¹*x₂) (y₁⁻¹*y₂) hxx hyy
  have hh : α q x₂=α q x₁*(y₁⁻¹*y₂) := by
    have he := congrArg (fun z => α q x₁*z) hq
    simpa only [map_mul,map_inv,mul_inv_cancel_left] using he
  refine ⟨⟨y₁*(α q x₁)⁻¹,q⟩,?_,?_⟩
  · simp [smul_apply,mul_assoc]
  · simp [smul_apply,hh,mul_assoc]

end FiniteAlgebraicEnvelopes.AffinePermutation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

instance elementary_finitelyGenerated : Group.FG (Steinberg.ElementaryGroup (R s h (ZMod 2))) :=
  Group.fg_of_surjective Steinberg.elementaryQuotient_surjective

instance linearTorus_finitelyGenerated : Group.FG (LinearTorus s h) :=
  SequentialLimit.torus_finitelyGenerated _

theorem fullLinearAction_injective : Function.Injective (fullLinearAction s h) :=
  NonunitalTensor.torusAction_injective (phi s h (ZMod 2))
  (phi_injective s h (ZMod 2)) (phi_one_ne_one s h (ZMod 2))
  (detectingElement s h (ZMod 2)) (fixed_tensor_detector s h (ZMod 2))

theorem fullLinear_transitive (v w : ColumnSpace s h) (hv : v≠1) (hw : w≠1) :
    ∃ a : LinearTorus s h, fullLinearAction s h a v=w := by
  obtain ⟨x,hx⟩ := linear_transitive s h v w hv hw
  refine ⟨SemidirectProduct.inl x,?_⟩
  exact hx

instance fullAction_faithful : FaithfulSMul (FullGroup s h) (ColumnSpace s h) :=
  AffinePermutation.faithful (fullLinearAction s h) (fullLinearAction_injective s h)

theorem fullAction_two_transitive (x₁ x₂ y₁ y₂ : ColumnSpace s h) (hx : x₁≠x₂) (hy : y₁≠y₂) :
    ∃ a : FullGroup s h, a • x₁=y₁ ∧ a • x₂=y₂ :=
  AffinePermutation.two_transitive (fullLinearAction s h) (fullLinear_transitive s h) x₁ x₂ y₁ y₂ hx hy

instance fullAction_stabilizer_fg (x : ColumnSpace s h) :
    Group.FG (MulAction.stabilizer (FullGroup s h) x) :=
  AffinePermutation.stabilizer_finitelyGenerated (fullLinearAction s h) x

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Steinberg
open scoped commutatorElement
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

theorem singleDiagonal_injective (p : ι) : Function.Injective (singleDiagonal (R:=R) p) := by
  intro a b he
  apply Units.ext
  have hh := congrArg (fun m : (Matrix ι ι R)ˣ => m.val p p) he
  simpa only [singleDiagonal_val,Matrix.diagonal_apply_eq,ite_true] using hh

variable {G : Type*} [_root_.Group G]

theorem inputDiagonal_injective (f : G×G →* Rˣ) (hf : Function.Injective f) : Function.Injective (inputDiagonal f) :=
  (singleDiagonal_injective 0).comp (hf.comp (by intro x y he; exact congrArg Prod.fst he))

theorem elementaryEmbedding_injective (f : G×G →* Rˣ) (hf : Function.Injective f) (b : Rˣ)
    (hc : ∀ g : G, ⁅f (g,g),b⁆=f (g,1)) : Function.Injective (elementaryEmbedding f b hc) := by
  intro x y he
  exact inputDiagonal_injective f hf (congrArg Subtype.val he)

end FiniteAlgebraicEnvelopes.Steinberg

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H] {n : ℕ} (s : Fin n → H)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (hs : Subgroup.closure (Set.range s)=⊤)
variable (f : G×G →* H) (t : H) (hc : ∀ g : G, ⁅f (g,g),t⁆=f (g,1))

theorem elementaryInput_injective (hf : Function.Injective f) :
    Function.Injective (elementaryInput s h hs f t hc) := by
  apply Steinberg.elementaryEmbedding_injective
  exact (coefficientUnits_injective s h (ZMod 2) hs).comp hf

theorem elementaryInFull_injective : Function.Injective (elementaryInFull s h) :=
  SemidirectProduct.inr_injective.comp (SemidirectProduct.inl_injective.comp
    (SequentialLimit.of_injective _ (linearTransition_injective s h (ZMod 2)) 0))

theorem inputInFull_injective (hf : Function.Injective f) : Function.Injective (inputInFull s h hs f t hc) :=
  (elementaryInFull_injective s h).comp (elementaryInput_injective s h hs f t hc hf)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

section
namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

instance steinberg_finitelyPresented : Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (R s h (ZMod 2))) :=
  steinberg_finitePresentation_of_free s h (ZMod 2)

instance affine_finitelyPresented :
    Group.IsFinitelyPresented (AffineAction.Group (R:=R s h (ZMod 2)) (V:=BigAlgebra s h (ZMod 2))) :=
  Enveloping.affine_finitePresentation (bigGenerators s h (ZMod 2))
    (bigGenerators_finite s h (ZMod 2)) (bigGenerators_generate s h (ZMod 2))

instance full_finitelyPresented : Group.IsFinitelyPresented (FullGroup s h) := by
  let := MappingTorus.torus_finitelyPresented (affineTransition s h)
  exact Group.IsFinitelyPresented.equiv (affineTorusEquivalence s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes
/-- The source's complete action envelope, in a small universe. -/
theorem input_finite_action_envelope {G : Type*} [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (Γ : Type) (_ : Group Γ) (X : Type) (_ : MulAction Γ X),
      Group.IsFinitelyPresented Γ ∧ Countable X ∧ Infinite X ∧ FaithfulSMul Γ X ∧
      (∀ x₁ x₂ y₁ y₂ : X, x₁≠x₂ → y₁≠y₂ → ∃ g : Γ, g • x₁=y₁ ∧ g • x₂=y₂) ∧
      (∀ x : X, Group.FG (MulAction.stabilizer Γ x)) ∧
      ∃ f : G →* Γ, Function.Injective f := by
  obtain ⟨H,_,_,⟨n,s,hs,h⟩,f,t,hf,hc⟩ := group_input G hG
  refine ⟨Bootstrap.Source.FullGroup s h,inferInstance,Bootstrap.Source.ColumnSpace s h,
    inferInstance,inferInstance,inferInstance,Bootstrap.Source.columnSpace_infinite s h,inferInstance,
    Bootstrap.Source.fullAction_two_transitive s h,?_,
    Bootstrap.Source.inputInFull s h hs f t hc,Bootstrap.Source.inputInFull_injective s h hs f t hc hf⟩
  intro x
  exact Bootstrap.Source.fullAction_stabilizer_fg s h x

end FiniteAlgebraicEnvelopes
end

namespace FiniteAlgebraicEnvelopes

section
universe u

/-- Manuscript Theorem 1.2, with the exact frozen universe and action requirements. -/
theorem envelope_oai (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) : HasActionEnvelope G := by
  obtain ⟨Γ,hΓ,X,hX,hfp,hcount,hinf,hfaith,htwo,hstab,f,hf⟩ := input_finite_action_envelope hG
  let : MulAction (ULift.{u} Γ) (ULift.{u} X) := LiftedAction.action
  let : Group.IsFinitelyPresented (ULift.{u} Γ) :=
    Group.IsFinitelyPresented.equiv (MulEquiv.ulift.symm : Γ ≃* ULift.{u} Γ)
  refine ⟨ULift.{u} Γ,inferInstance,ULift.{u} X,inferInstance,inferInstance,inferInstance,
    inferInstance,LiftedAction.faithful,?_,?_,(MulEquiv.ulift.symm.toMonoidHom).comp f,
    MulEquiv.ulift.symm.injective.comp hf⟩
  · intro x₁ x₂ y₁ y₂ hx hy
    obtain ⟨g,hg₁,hg₂⟩ := htwo x₁.down x₂.down y₁.down y₂.down
      (fun h => hx (ULift.ext _ _ h)) (fun h => hy (ULift.ext _ _ h))
    refine ⟨ULift.up g,?_,?_⟩
    · apply ULift.ext; exact hg₁
    · apply ULift.ext; exact hg₂
  · intro x
    let := hstab x.down
    let e : MulAction.stabilizer Γ x.down ≃* MulAction.stabilizer (ULift.{u} Γ) x :=
      (LiftedAction.stabilizerEquivalence x).symm
    exact Group.fg_of_surjective (f:=e.toMonoidHom) (show Function.Surjective e.toMonoidHom from e.surjective)

open scoped commutatorElement

end

end FiniteAlgebraicEnvelopes

end

end OAI
end

theorem solution.{u} : type_of% @OAI.FiniteAlgebraicEnvelopes.envelope_oai.{u} := @OAI.FiniteAlgebraicEnvelopes.envelope_oai.{u}
