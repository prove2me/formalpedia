-- Prove2me | solution 1 for OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:21:12.762916+00:00
-- url     : https://prove2.me/submissions/57c2f707-582d-4c6c-b412-accfd8dd7d35

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C038
import Definitions.Def_OAIQ039C040
import Theorems.Thm_OAI_Kadison_IrreducibleTowerAveraging_hull_bounded
import Theorems.Thm_OAI_Kadison_IrreducibleTowerAveraging_hull_trace
import Theorems.Thm_OAI_Kadison_NormalRelativeCommutant_commutes_of_fixed

section
-- module Solutions.OAIQ039_CM.Commutator_ConvexIsometryFix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConvexIsometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_fixed (K : Set H) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconv : Convex ℝ K) :
    ∃ z∈K, ∀ U : H →ₗᵢ[ℂ] H, (∀ x∈K, U x∈K) → U z=z := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨z,hz,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv (0:H)
  refine ⟨z,hz,?_⟩
  intro U hUK
  have huz := hUK z hz
  have hmin' : ‖(0:H)-U z‖=⨅ w : K, ‖(0:H)-(w:H)‖ := by
    simpa only [zero_sub,norm_neg,U.norm_map] using hmin
  have ha := (norm_eq_iInf_iff_real_inner_le_zero hconv hz).mp hmin (U z) huz
  have hb := (norm_eq_iInf_iff_real_inner_le_zero hconv huz).mp hmin' z hz
  have hc : ‖U z-z‖^2=‖U z‖^2-2*inner ℝ (U z) z+‖z‖^2 := norm_sub_sq_real _ _
  simp only [zero_sub,inner_neg_left,inner_sub_right,real_inner_self_eq_norm_sq] at ha hb
  have he : inner ℝ z (U z)=inner ℝ (U z) z := real_inner_comm _ _
  rw [he] at ha
  have hd : ‖U z-z‖=0 := by nlinarith [norm_nonneg (U z-z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hd)

omit [CompleteSpace H] in
lemma maps_closedConvexHull (U : H →ₗᵢ[ℂ] H) (S : Set H)
    (hU : ∀ x∈S, U x∈S) :
    ∀ x∈closedConvexHull ℝ S, U x∈closedConvexHull ℝ S := by
  have hconv : Convex ℝ (U ⁻¹' closedConvexHull ℝ S) :=
    convex_closedConvexHull.linear_preimage (U.toLinearMap.restrictScalars ℝ)
  have hcl : IsClosed (U ⁻¹' closedConvexHull ℝ S) :=
    isClosed_closedConvexHull.preimage U.continuous
  exact closedConvexHull_min (fun x hx => subset_closedConvexHull (hU x hx)) hconv hcl

end Kadison.ConvexIsometry

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IrreducibleTowerAveraging
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.IrreducibleTowerAveraging

open TracialGNS NormalGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

omit [∀ n, Nonempty (ι n)] in
lemma orbit_self (a : M) : algebraVector τ a ∈ orbit M τ stage hmono a := by
  refine ⟨1,?_⟩
  simp

omit [∀ n, Nonempty (ι n)] in
lemma conjugation_orbit (a : M) (u : stageUnitaries M stage hmono) :
    ∀ x∈orbit M τ stage hmono a,
      conjugation τ hτ u.val x∈orbit M τ stage hmono a := by
  rintro x ⟨v,rfl⟩
  refine ⟨u*v,?_⟩
  simp only [algebraVector_apply,conjugation_coe,Submonoid.coe_mul,
    star_mul,mul_assoc]

include hτ in
omit [∀ n, Nonempty (ι n)] in
theorem scalar_mem_hull_oai
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) (ha : ‖a‖≤1) :
    (τ a) • vacuum τ ∈ closedConvexHull ℝ (orbit M τ stage hmono a) := by
  obtain ⟨z,hz,hfix⟩ := ConvexIsometry.exists_fixed
    (closedConvexHull ℝ (orbit M τ stage hmono a))
    ⟨algebraVector τ a,subset_closedConvexHull (orbit_self M τ stage hmono a)⟩
    isClosed_closedConvexHull convex_closedConvexHull
  obtain ⟨b,_,hb⟩ := hull_bounded M τ stage hmono hnormal a ha hz
  have hcomm (n : ℕ) (x : Matrix (ι n) (ι n) ℂ) : stage n x*b=b*stage n x := by
    apply NormalRelativeCommutant.commutes_of_fixed M τ hτ (stage n) b hfaith _ x
    intro u
    let v : stageUnitaries M stage hmono :=
      ⟨NormalRelativeCommutant.liftedUnitary M (stage n) u, n, ⟨u,rfl⟩⟩
    rw [hb]
    exact hfix _ (ConvexIsometry.maps_closedConvexHull _ _
      (conjugation_orbit M τ hτ stage hmono a v))
  obtain ⟨c,hc⟩ := hirr b hcomm
  have htc : τ b=c := by
    rw [hc,Algebra.algebraMap_eq_smul_one,map_smul,hone,smul_eq_mul,mul_one]
  have hta : τ b=τ a := by
    rw [←inner_vacuum_algebraVector,hb]
    exact hull_trace M τ hτ stage hmono a z hz
  have hz' : z=(τ a) • vacuum τ := by
    rw [←hb,hc,Algebra.algebraMap_eq_smul_one,map_smul,←hta,htc]
    rfl
  rwa [hz'] at hz

end Kadison.IrreducibleTowerAveraging

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull_oai.{u_1, u_2} := @OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull_oai.{u_1, u_2}
