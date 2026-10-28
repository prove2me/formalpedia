-- Prove2me | solution 1 for OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:22:42.972217+00:00
-- url     : https://prove2.me/submissions/3754278f-a123-4f91-bf97-0dbe23e43eba

import Mathlib
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C039
import Theorems.Thm_OAI_Kadison_CompactInvariant_exists_fixed_point

section
-- module Solutions.OAIQ039_CM.Commutator_WeakDualHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology ComplexOrder

namespace Kadison.WeakDualHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] OAI.Kadison.WeakDualHull.instAddCommGroupWeakDualComplex_solutions
attribute [local instance] OAI.Kadison.WeakDualHull.instModuleRealWeakDualComplex_solutions
lemma subset_hull (S : Set (WeakDual ℂ E)) : S⊆hull S :=
  (subset_convexHull ℝ S).trans subset_closure

lemma convex_hull (S : Set (WeakDual ℂ E)) : Convex ℝ (hull S) :=
  (convex_convexHull ℝ S).closure

lemma eval_norm_le {S : Set (WeakDual ℂ E)} (a : E) (R : ℝ)
    (h : ∀ f∈S,‖f a‖≤R) {f : WeakDual ℂ E} (hf : f∈hull S) : ‖f a‖≤R := by
  have hc : IsClosed {f : WeakDual ℂ E | ‖f a‖≤R} :=
    isClosed_le (WeakDual.eval_continuous a).norm continuous_const
  have hv : Convex ℝ {f : WeakDual ℂ E | ‖f a‖≤R} := by
    intro g hg k hk s t hs ht hst
    change ‖s • g a+t • k a‖≤R
    calc
      _ ≤ ‖s • g a‖+‖t • k a‖ := norm_add_le _ _
      _ = s*‖g a‖+t*‖k a‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg hs,abs_of_nonneg ht]
      _ ≤ s*R+t*R := add_le_add (mul_le_mul_of_nonneg_left hg hs)
        (mul_le_mul_of_nonneg_left hk ht)
      _ = R := by rw [←add_mul,hst,one_mul]
  exact closure_minimal (convexHull_min h hv) hc hf

lemma norm_le {S : Set (WeakDual ℂ E)} (R : ℝ) (hR : 0≤R)
    (h : ∀ f∈S,‖f.toStrongDual‖≤R) {f : WeakDual ℂ E} (hf : f∈hull S) :
    ‖f.toStrongDual‖≤R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro a
  exact eval_norm_le a (R*‖a‖) (fun g hg =>
    (g.toStrongDual.le_opNorm a).trans (mul_le_mul_of_nonneg_right (h g hg) (norm_nonneg a))) hf

lemma compact_hull {S : Set (WeakDual ℂ E)} (R : ℝ) (hR : 0≤R)
    (h : ∀ f∈S,‖f.toStrongDual‖≤R) : IsCompact (hull S) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ E) R).of_isClosed_subset isClosed_closure
  intro f hf
  simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using norm_le R hR h hf

end Kadison.WeakDualHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrbitStateHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma vector_norm (x : H) : ‖vector M x‖≤‖x‖*‖x‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_self_nonneg _) _

lemma vector_mem_hull (x : H) : (vector M x).toWeakDual∈hull M x := by
  apply WeakDualHull.subset_hull
  exact ⟨1,M.one_mem,rfl⟩

lemma hull_nonempty (x : H) : (hull M x).Nonempty := ⟨_,vector_mem_hull M x⟩

lemma hull_compact (x : H) : IsCompact (hull M x) := by
  apply WeakDualHull.compact_hull (‖x‖*‖x‖) (mul_self_nonneg _)
  rintro f ⟨u,_,rfl⟩
  simpa only [StrongDual.toStrongDual_toWeakDual,Unitary.norm_map] using vector_norm M ((u : H →L[ℂ] H) x)

end Kadison.OrbitStateHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryDualAction
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.UnitaryDualAction

variable {A : Type*} [CStarAlgebra A]

lemma conjugate_norm (u : unitary A) (a : A) :
    ‖star (u:A)*a*(u:A)‖=‖a‖ := by
  rw [CStarRing.norm_mul_coe_unitary]
  exact CStarRing.norm_coe_unitary_mul (star u) a

lemma act_norm_le (u : unitary A) (f : WeakDual ℂ A) :
    ‖(u • f).toStrongDual‖≤‖f.toStrongDual‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  change ‖f.toStrongDual (star (u:A)*a*(u:A))‖≤‖f.toStrongDual‖*‖a‖
  simpa only [conjugate_norm] using f.toStrongDual.le_opNorm (star (u:A)*a*(u:A))

lemma act_norm (u : unitary A) (f : WeakDual ℂ A) :
    ‖(u • f).toStrongDual‖=‖f.toStrongDual‖ := by
  apply (act_norm_le u f).antisymm
  have h := act_norm_le u⁻¹ (u • f)
  simpa only [inv_smul_smul] using h

lemma act_sub (u : unitary A) (f g : WeakDual ℂ A) : u • (f-g)=u • f-u • g := by
  apply weak_ext
  intro a
  rfl

lemma act_dist (u : unitary A) (f g : WeakDual ℂ A) :
    dist (u • f).toStrongDual (u • g).toStrongDual=dist f.toStrongDual g.toStrongDual := by
  rw [dist_eq_norm,dist_eq_norm]
  have he : (u • f).toStrongDual-(u • g).toStrongDual=(u • (f-g)).toStrongDual := by
    rw [act_sub,map_sub]
  rw [he,act_norm,map_sub]

lemma act_linear (u : unitary A) :
    ∃ L : WeakDual ℂ A →ₗ[ℝ] WeakDual ℂ A,∀ f,L f=u • f := by
  exact ⟨{ toFun := fun f => u • f
           map_add' := fun f g => by apply weak_ext; intro a; rfl
           map_smul' := fun c f => by apply weak_ext; intro a; rfl },fun _ => rfl⟩

theorem trace_of_fixed (f : WeakDual ℂ A) (hf : ∀ u : unitary A,u • f=f) :
    ∀ a b : A,f (a*b)=f (b*a) := by
  intro a b
  let L : A →ₗ[ℂ] ℂ := f.toStrongDual.toLinearMap.comp (LinearMap.mulRight ℂ b)
  let R : A →ₗ[ℂ] ℂ := f.toStrongDual.toLinearMap.comp (LinearMap.mulLeft ℂ b)
  have hEq : L=R := by
    apply LinearMap.ext_on (CStarAlgebra.span_unitary A)
    intro v hv
    let u : unitary A := ⟨v,hv⟩
    have h := congrArg (fun g : WeakDual ℂ A => g (v*b)) (hf u)
    change f (star v*(v*b)*v)=f (v*b) at h
    have he : star v*(v*b)*v=b*v := by
      rw [←mul_assoc (star v) v b,hv.1,one_mul]
    rw [he] at h
    exact h.symm
  exact congrArg (fun T : A →ₗ[ℂ] ℂ => T a) hEq

end Kadison.UnitaryDualAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrbitFixedTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.OrbitStateHull

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma act_vector (u : unitary M) (x : H) :
    u • (vector M x).toWeakDual=(vector M (((u:M):H →L[ℂ] H) x)).toWeakDual := by
  apply UnitaryDualAction.weak_ext
  intro a
  change inner ℂ x ((star ((u:M):H →L[ℂ] H)) (((a:M):H →L[ℂ] H) (((u:M):H →L[ℂ] H) x))) =
    inner ℂ (((u:M):H →L[ℂ] H) x) (((a:M):H →L[ℂ] H) (((u:M):H →L[ℂ] H) x))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

lemma orbit_invariant (x : H) : CompactInvariant.Invariant (G:=unitary M) (orbit M x) := by
  intro u f hf
  obtain ⟨v,hv,rfl⟩ := hf
  let w : unitary (H →L[ℂ] H) := ⟨((u:M):H →L[ℂ] H),by
    constructor
    · exact congrArg (fun a : M => (a:H →L[ℂ] H)) u.property.1
    · exact congrArg (fun a : M => (a:H →L[ℂ] H)) u.property.2⟩
  refine ⟨w*v,M.mul_mem (u:M).property hv,?_⟩
  exact act_vector M u ((v:H →L[ℂ] H) x)

lemma hull_invariant (x : H) : CompactInvariant.Invariant (G:=unitary M) (hull M x) := by
  intro u f hf
  obtain ⟨L,hL⟩ := UnitaryDualAction.act_linear u
  have hLcont : Continuous L := by
    have he : (L : WeakDual ℂ M → WeakDual ℂ M)=(fun f => u • f) := funext hL
    rw [he]
    exact continuous_const_smul u
  have hmap : L '' convexHull ℝ (orbit M x) ⊆ convexHull ℝ (orbit M x) := by
    rw [L.image_convexHull]
    apply convexHull_mono
    rintro _ ⟨g,hg,rfl⟩
    rw [hL]
    exact orbit_invariant M x u g hg
  have hpre : closure (convexHull ℝ (orbit M x)) ⊆ L ⁻¹' closure (convexHull ℝ (orbit M x)) :=
    closure_minimal (fun g hg => subset_closure (hmap ⟨g,hg,rfl⟩))
      (isClosed_closure.preimage hLcont)
  have he := hpre hf
  change L f∈hull M x at he
  rwa [hL] at he

theorem exists_tracial_hull_of_norm_separable_oai (x : H)
    (hsep : TopologicalSpace.IsSeparable (WeakDual.toStrongDual '' hull M x)) :
    ∃ f : WeakDual ℂ M, f∈hull M x ∧ ∀ a b : M,f (a*b)=f (b*a) := by
  let j : WeakDual ℂ M ≃ₗ[ℝ] StrongDual ℂ M :=
    { toFun := WeakDual.toStrongDual
      invFun := StrongDual.toWeakDual
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Continuous j.symm := by
    apply WeakDual.continuous_of_continuous_eval
    intro a
    change Continuous (fun f : StrongDual ℂ M => f a)
    exact (ContinuousLinearMap.apply ℂ ℂ a).continuous
  have hb : ∀ y : StrongDual ℂ M,∀ r : ℝ,IsClosed {f : WeakDual ℂ M | dist (j f) y ≤ r} := by
    intro y r
    change IsClosed (WeakDual.toStrongDual ⁻¹' Metric.closedBall y r)
    exact WeakDual.isClosed_closedBall y r
  obtain ⟨f,hf,hfix⟩ := CompactInvariant.exists_fixed_point j hj hb
    (fun u f g => UnitaryDualAction.act_dist u f g) (hull_compact M x)
    (hull_nonempty M x) (WeakDualHull.convex_hull (orbit M x)) (hull_invariant M x) hsep
  exact ⟨f,hf,UnitaryDualAction.trace_of_fixed f hfix⟩

end Kadison.OrbitStateHull

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable_oai.{u_1} := @OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable_oai.{u_1}
