-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.exists_almost_full_finite_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:56:33.338949+00:00
-- url     : https://prove2.me/submissions/0c170c8b-6ea5-4612-9b1c-31a3898a19b8

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_FinitePatching_Words_momentBound_add
import Theorems.Thm_OAI_Kadison_FinitePatching_admissible_chain_upper
import Theorems.Thm_OAI_Kadison_FinitePatching_exists_finite_word_patch

section
-- module Solutions.OAIQ039_CM.Commutator_ExponentialMomentBudget
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FinitePatching

lemma momentBudget_nonneg {ε : ℝ} (hε : 0 ≤ ε) (K t : ℝ) : 0 ≤ momentBudget ε K t :=
  mul_nonneg hε (Real.exp_pos _).le

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialMomentBudget
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

omit [StarOrderedRing A] in
lemma zero_word_trace (hcenter : ∀ j,τ (x j)=0) (l : List (Letter J K))
    (hne : l≠[]) (hv : Valid l) : τ (word x k PartialUnitary.zero l)=0 := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons i l =>
    cases l with
    | nil =>
      rcases i with ⟨j,s⟩
      cases s with
      | none => simpa [letter,slotPower] using hcenter j
      | some s =>
        cases s <;> simp only [word_cons,word_nil,letter,slotPower,PartialUnitary.zero_power,
          mul_zero,mul_one,map_zero]
        simp [PartialUnitary.zero]
    | cons j l =>
      obtain ⟨a,ha⟩ := hv [] i (j::l) rfl (by simp)
      simp [word_cons,letter,ha,slotPower]

omit [StarOrderedRing A] in
lemma zero_momentBound (hcenter : ∀ j,τ (x j)=0) (N : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    MomentBound τ x k PartialUnitary.zero N B := by
  constructor
  · intro i; simpa using hB
  · intro l hl hlen hv
    simpa only [zero_word_trace τ x k hcenter l hl hv,norm_zero] using hB

end Kadison.FinitePatching.Words

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryOrder
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma le_add (v w : PartialUnitary A) (h : v.support*w.support=0) : v ≤ v.add w h := by
  refine ⟨le_add_of_nonneg_right w.projection.nonneg,?_⟩
  change (v.val+w.val)*v.support=v.val
  have hz := power_mul_power_zero (orthogonal_support_symm h) 1 0
  simp [power] at hz
  rw [add_mul,v.mul_support,hz,add_zero]

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteWordMaximalPatching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
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

variable (M R : VonNeumannAlgebra H)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {J K : Type*} (x : J → M) (k : K → ℤ)

lemma zero_admissible (hcenter : ∀ j,τ (x j)=0) (N : ℕ) {ε η : ℝ}
    (hε : 0 ≤ ε) (hη : η ≤ 1) : PartialUnitary.zero∈Admissible M R τ x k N ε η := by
  refine ⟨R.zero_mem,?_,zero_momentBound τ x k hcenter N (momentBudget_nonneg hε _ _)⟩
  change (τ 0).re ≤ 1-η
  simp only [map_zero,Complex.zero_re]
  linarith

variable [Fintype J] [Fintype K]

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem exists_almost_full_finite_tests_oai (hRM : R ≤ M)
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (hx : ∀ j,‖x j‖ ≤ 1) (hcenter : ∀ j,τ (x j)=0) (hk : ∀ i,k i≠0)
    (N : ℕ) {ε η : ℝ} (hε : 0<ε) (hη : 0<η) (hη1 : η ≤ 1) :
    ∃ v : PartialUnitary M, (v.val : H →L[ℂ] H)∈R ∧ (τ v.support).re=1-η ∧
      MomentBound τ x k v N (momentBudget ε (budgetSlope N η) (1-η)) := by
  have hzero := zero_admissible M R τ x k hcenter N hε.le hη1
  obtain ⟨v,hv⟩ := zorn_le₀ (Admissible M R τ x k N ε η) (by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with he | hne
    · exact ⟨PartialUnitary.zero,hzero,fun w hw => (he ▸ hw : w∈(∅ : Set (PartialUnitary M))).elim⟩
    · exact admissible_chain_upper M R τ hτ x k hnormal hone hx N ε η c hcs hc hne)
  have hcut : (τ v.support).re=1-η := by
    apply le_antisymm hv.1.2.1
    by_contra hn
    have hlt : (τ v.support).re<1-η := lt_of_not_ge hn
    have hrest : η ≤ (τ (1-v.support)).re := by
      rw [map_sub,hone,Complex.sub_re,Complex.one_re]
      linarith [hv.1.2.1]
    have hvR : (v.support : H →L[ℂ] H)∈R := by
      rw [←v.star_mul]
      exact R.mul_mem (R.star_mem' hv.1.1) hv.1.1
    obtain ⟨w,hwR,_,hqp,horth,hqt,hqsmall,hpure,hsmall,hphase⟩ :=
      exists_finite_word_patch M R hRM τ hτ stage hmono hnormal hfaith hone hirr hgrow hstage
        hdiffuse x k hk v hvR (hη.trans_le hrest) N hε
        (show 0<1-η-(τ v.support).re by linarith)
    have hnew : v.add w horth∈Admissible M R τ x k N ε η := by
      refine ⟨R.add_mem hv.1.1 hwR,?_,?_⟩
      · change (τ (v.support+w.support)).re ≤ 1-η
        rw [map_add,Complex.add_re]
        linarith
      · exact momentBound_add τ hτ x k hx v w horth hqp hε.le hη hrest hv.1.2.2
          hpure hsmall hphase
    have hp := (hv.2 hnew (v.le_add w horth)).1
    have htp := (τ.monotone hp).1
    change (τ (v.support+w.support)).re ≤ (τ v.support).re at htp
    rw [map_add,Complex.add_re] at htp
    linarith
  exact ⟨v,hv.1.1,hcut,by simpa only [hcut] using hv.1.2.2⟩

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.FinitePatching.exists_almost_full_finite_tests_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.FinitePatching.exists_almost_full_finite_tests_oai.{u_1, u_2, u_3, u_4}
