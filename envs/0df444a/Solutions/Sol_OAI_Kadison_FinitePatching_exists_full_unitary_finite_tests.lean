-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.exists_full_unitary_finite_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:52:40.7626+00:00
-- url     : https://prove2.me/submissions/867ab8d2-e3f0-4f25-8b61-c6660a3d7438

import Mathlib
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_FinitePatching_Words_momentBound_completed
import Theorems.Thm_OAI_Kadison_FinitePatching_exists_almost_full_finite_tests

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryCompletion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma ofUnitary_completion (v : PartialUnitary A) : ofUnitary v.completion=v.completed := by
  apply ext
  rfl

lemma completed_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M R : VonNeumannAlgebra H) (v : PartialUnitary M) (hv : (v.val : H →L[ℂ] H)∈R) :
    (v.completed.val : H →L[ℂ] H)∈R := by
  have hs : (v.support : H →L[ℂ] H)∈R := by
    rw [←v.star_mul]
    exact R.mul_mem (R.star_mem' hv) hv
  exact R.add_mem hv (R.sub_mem R.one_mem hs)

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestCompletion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

lemma slotCost_le {m : ℕ} (hk : ∀ i,(k i).natAbs ≤ m) (s : Slot K) : slotCost k s ≤ m+2 := by
  cases s with
  | none => simp [slotCost]
  | some s =>
    cases s with
    | none => simp [slotCost]
    | some i => exact Nat.add_le_add_right (hk i) 2

lemma wordCost_le {m : ℕ} (hk : ∀ i,(k i).natAbs ≤ m) (l : List (Letter J K)) :
    wordCost k l ≤ l.length*(m+2) := by
  induction l with
  | nil => simp [wordCost]
  | cons i l ih =>
    have hh := Nat.add_le_add (slotCost_le k hk i.2) ih
    simpa only [wordCost,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,
      one_mul,Nat.add_comm] using hh

omit [StarOrderedRing A] in
lemma momentBound_mono {v : PartialUnitary A} {N : ℕ} {B C : ℝ}
    (hB : MomentBound τ x k v N B) (hBC : B ≤ C) : MomentBound τ x k v N C :=
  ⟨fun i => (hB.1 i).trans hBC,fun l hl hn hv => (hB.2 l hl hn hv).trans hBC⟩

end Kadison.FinitePatching.Words

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFullUnitaryTests
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_full_unitary_finite_tests_oai {J K : Type*} [Fintype J] [Fintype K]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (x : J → M) (k : K → ℤ) (hx : ∀ j,‖x j‖ ≤ 1)
    (hcenter : ∀ j,τ (x j)=0) (hk : ∀ i,k i≠0)
    (N : ℕ) {α : ℝ} (hα : 0<α) :
    ∃ u : unitary M, ((u:M) : H →L[ℂ] H)∈R ∧
      MomentBound τ x k (PartialUnitary.ofUnitary u) N α := by
  classical
  let m := Finset.univ.sup (fun i => (k i).natAbs)
  have hkm (i : K) : (k i).natAbs ≤ m := Finset.le_sup (f := fun i : K => (k i).natAbs) (s:=Finset.univ) (by simp)
  let C : ℝ := ((N+1)*(m+2):ℕ)
  have hC : 0<C := by dsimp [C]; positivity
  have hp (i : K) : ((k i).natAbs:ℝ)+2 ≤ C := by
    have h1 := Nat.add_le_add_right (hkm i) 2
    have h2 : m+2 ≤ (N+1)*(m+2) := by nlinarith
    dsimp [C]
    exact_mod_cast h1.trans h2
  have hw (l : List (Letter J K)) (hl : l.length ≤ N) : (wordCost k l:ℝ) ≤ C := by
    apply Nat.cast_le.mpr
    exact (wordCost_le k hkm l).trans (Nat.mul_le_mul_right (m+2) (hl.trans (Nat.le_succ N)))
  let r : ℝ := min 1 (α/(4*C))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := min_le_left _ _
  have hCr : C*r ≤ α/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*C)).mp (min_le_right 1 (α/(4*C)))
    change r*(4*C) ≤ α at hh
    nlinarith
  let η := r^2
  have hη : 0<η := sq_pos_of_pos hr
  have hη1 : η ≤ 1 := by dsimp [η]; nlinarith
  let ε := α/(4*Real.exp (budgetSlope N η*(1-η)))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hbudget : momentBudget ε (budgetSlope N η) (1-η)=α/4 := by
    dsimp [momentBudget,ε]
    field_simp
  obtain ⟨v,hvR,hcut,hbound⟩ := exists_almost_full_finite_tests M R τ hτ x k stage hmono
    hRM hnormal hfaith hone hirr hgrow hstage hdiffuse hx hcenter hk N hε hη hη1
  have hfull := momentBound_completed τ hτ x k hone hx v hbound hp hw
  have htotal : momentBudget ε (budgetSlope N η) (1-η)+C*Real.sqrt (1-(τ v.support).re) ≤ α := by
    rw [hbudget,hcut,show 1-(1-η)=η by ring]
    change α/4+C*Real.sqrt (r^2) ≤ α
    rw [Real.sqrt_sq hr.le]
    linarith
  refine ⟨v.completion,v.completed_mem M R hvR,?_⟩
  rw [PartialUnitary.ofUnitary_completion]
  exact momentBound_mono τ x k hfull htotal

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.FinitePatching.exists_full_unitary_finite_tests_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.FinitePatching.exists_full_unitary_finite_tests_oai.{u_1, u_2, u_3, u_4}
