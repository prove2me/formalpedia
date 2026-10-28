-- Prove2me | solution 1 for OAI.KirchbergRordam.PrimeDropPresentation.Channels.finite_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:38:51.869931+00:00
-- url     : https://prove2.me/submissions/50b4428c-92ec-4d75-8148-a4349752e5e8

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr014
import Definitions.Def_OAIB3Kr015
import Theorems.Thm_OAI_KirchbergRordam_PrimeDropPresentation_Channels_stageRight_bound

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_InductiveLimit
attribute [-instance] _root_.OAI.KirchbergRordam.PrimeDropPresentation.instSeparableSpaceObjSystem _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


open scoped TensorProduct CStarAlgebra


namespace KirchbergRordam.CStarInductiveLimit
section
universe u


attribute [instance] System.cstar


variable {C : Type*} [CStarAlgebra C]


theorem induction_on (S : System) {P : Algebra S → Prop} (x : Algebra S)
    (hclosed : IsClosed {x | P x}) (hof : ∀ n x, P (of S n x)) : P x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih x =>
    refine DirectLimit.induction S.map ?_ x
    exact hof


theorem denseRange_of (S : System) :
    DenseRange (fun p : Σ n, S.obj n => of S p.1 p.2) := by
  intro x
  exact induction_on S x isClosed_closure
    (fun n x => subset_closure ⟨⟨n,x⟩,rfl⟩)


instance instSeparableSpaceAlgebraOfObj (S : System) [∀ n, TopologicalSpace.SeparableSpace (S.obj n)] :
    TopologicalSpace.SeparableSpace (Algebra S) :=
  (denseRange_of S).separableSpace (continuous_sigma fun n => map_continuous (of S n))

end

universe u


attribute [instance] Chain.cstar


end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixPaths
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra


open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.MatrixDiagonalPath
open scoped ComplexOrder CStarAlgebra Matrix
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [instDecidableEqκ : DecidableEq κ] [Fintype ν] [DecidableEq ν]


omit instDecidableEqκ in
lemma interpolate_zero.{contextLevel1, contextLevel2}
    {κ : Type contextLevel1}
    {ν : Type contextLevel2}
    [Fintype κ]
    [DecidableEq κ]
    [Fintype ν]
    [DecidableEq ν]
    (e₀ e₁ : κ ≃ ν) (a : Mat κ) :
    interpolate e₀ e₁ 0 a = CStarMatrix.reindexₐ ℂ ℂ e₀ a := by
  simp only [interpolate, StarAlgEquiv.trans_apply, Path.source,
    MatrixPermutationPath.perm_one]
  simp

end KirchbergRordam.MatrixDiagonalPath


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedSystem
attribute [-instance] _root_.OAI.KirchbergRordam.MatrixTensor.matrixFinite _root_.OAI.KirchbergRordam.MatrixTensor.subCStar _root_.OAI.KirchbergRordam.MatrixTensor.subClosed _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam.MatrixBlockReindex
open MatrixDiagonalPath
open MatrixTensor (leftMatrix rightMatrix)
open scoped ComplexOrder CStarAlgebra Matrix
variable {P Q R S : Type*} [Fintype P] [Fintype Q] [Fintype R] [Fintype S]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [DecidableEq R] [DecidableEq S]
omit instDecidableEqP instDecidableEqQ in
lemma reindex_trans.{contextLevel1, contextLevel2}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    [Fintype P]
    [Fintype Q]
    [DecidableEq P]
    [DecidableEq Q]
    {T : Type*} [Fintype T] [DecidableEq T]
    (e : P ≃ Q) (f : Q ≃ T) (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (e.trans f) a =
      CStarMatrix.reindexₐ ℂ ℂ f (CStarMatrix.reindexₐ ℂ ℂ e a) := rfl
lemma reindex_left (e : P ≃ Q) (f : R ≃ S) (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (_root_.OAI.KirchbergRordam.MatrixTensor.leftMatrix (κ:=R) a) =
      _root_.OAI.KirchbergRordam.MatrixTensor.leftMatrix (κ:=S) (CStarMatrix.reindexₐ ℂ ℂ e a) := by
  ext i j
  rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
  change _root_.OAI.KirchbergRordam.MatrixTensor.leftMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
  simp only [left_apply, f.symm.injective.eq_iff]
  rfl
end KirchbergRordam.MatrixBlockReindex


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DiagonalIteration
attribute [-instance] _root_.OAI.KirchbergRordam.PrimeDropPresentation.instSeparableSpaceObjSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.DiagonalIteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
lemma conj_mul (u v : unitary A) (a : A) : conj (u*v) a=conj u (conj v a) := by
  simp [conj,Unitary.conjStarAlgAut_apply,mul_assoc]
lemma conj_star (u : unitary A) (a : A) : conj (star u) (conj u a)=a := by
  simp only [conj,Unitary.conjStarAlgAut_apply,Unitary.coe_star,star_star]
  rw [←mul_assoc,←mul_assoc,u.property.1,one_mul,mul_assoc,u.property.1,mul_one]
lemma normalize_cancel (u v : unitary A) (a : A) :
    conj (star (u*star v)) (conj u a)=conj v a := by
  rw [star_mul,star_star,conj_mul,conj_star]

lemma map_pi_conj {ι : Type*} [Fintype ι] (φ : (ι→A) →⋆ₐ[ℂ] B)
    (v : ι→unitary A) (a : ι→A) : φ (fun i => conj (v i) (a i)) =
      conj (Unitary.map (StarMonoidHom.ofClass φ) (piUnitary v)) (φ a) := by
  change φ ((fun i => (v i:A))*a*star (fun i => (v i:A)))=
    φ (fun i => (v i:A))*φ a*star (φ (fun i => (v i:A)))
  rw [map_mul,map_mul,map_star]

attribute [instance] System.cstar System.finite
namespace System
variable (S : System)

lemma full_eq (n k : ℕ) (f : unitInterval → S.obj n) (t : unitInterval) :
    S.full n k f t=conj (S.unitaryPath n k t) (S.flat n k f t) := by
  induction k generalizing t with
  | zero => exact (conj_one _).symm
  | succ k ih =>
    simp only [full,flat,unitaryPath,ih,map_pi_conj,conj_mul]
    rfl

lemma flat_bound (hlip : ∀ n i, LipschitzWith (1/2) (S.eigen n i))
    (n k : ℕ) (f : unitInterval → S.obj n) (ε r : ℝ) (hε : 0≤ε)
    (hf : ∀ s t : unitInterval, dist s t ≤ (1/2:ℝ)^k*r → ‖f s-f t‖≤ε)
    (s t : unitInterval) (hst : dist s t≤r) :
    ‖S.flat n k f s-S.flat n k f t‖≤ε := by
  induction k generalizing r s t with
  | zero => exact hf s t (by simpa using hst)
  | succ k ih =>
    rw [flat,flat,←map_sub]
    apply (NonUnitalStarAlgHom.norm_apply_le (S.diagonal (n+k)) _).trans
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    apply ih (r/2)
    · intro x y hxy
      apply hf x y
      convert hxy using 1; ring
    · calc
        dist (S.eigen (n+k) i s) (S.eigen (n+k) i t) ≤
            (1/2:ℝ)*dist s t := (hlip (n+k) i).dist_le_mul s t
        _ ≤ r/2 := by linarith

lemma flat_eventually_small (hlip : ∀ n i, LipschitzWith (1/2) (S.eigen n i))
    (n : ℕ) (f : C(unitInterval,S.obj n)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ s t : unitInterval, ‖S.flat n k f s-S.flat n k f t‖≤ε := by
  obtain ⟨δ,hδ,hf⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hp.eventually (gt_mem_nhds hδ)] with k hk s t
  apply S.flat_bound hlip n k f ε 1 hε.le
  · intro x y hxy
    apply le_of_lt
    rw [←dist_eq_norm]
    apply hf
    exact lt_of_le_of_lt (by simpa using hxy) hk
  · change |(s:ℝ)-(t:ℝ)|≤1
    exact abs_le.mpr ⟨by linarith [s.property.1,t.property.2],by linarith [s.property.2,t.property.1]⟩
end System
end KirchbergRordam.DiagonalIteration
namespace KirchbergRordam.CStarInductiveLimit
lemma approximation_common_stage (S : System) (F : Finset (Algebra S)) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, ∃ a : Algebra S → S.obj n, ∀ x∈F, ‖of S n (a x)-x‖<ε := by
  classical
  choose v hv using fun x : Algebra S => (denseRange_of S).exists_dist_lt x hε
  let n := F.sup (fun x => (v x).1)
  let a : Algebra S → S.obj n := fun x => if hx : x∈F then
    S.map (v x).1 n (Finset.le_sup (f:=fun x => (v x).1) hx) (v x).2 else 0
  refine ⟨n,a,fun x hx => ?_⟩
  dsimp only [a]
  rw [dite_eq_left hx,of_map]
  simpa only [dist_eq_norm,norm_sub_rev] using hv x
end KirchbergRordam.CStarInductiveLimit
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_EndpointMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.EndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration
open scoped ComplexOrder CStarAlgebra
variable {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
lemma map_conj (φ : A →⋆ₐ[ℂ] B) (u : unitary A) (a : A) :
    φ (conj u a) = conj (Unitary.map (StarMonoidHom.ofClass φ) u) (φ a) := by
  change φ ((u:A)*a*star (u:A)) = φ (u:A)*φ a*star (φ (u:A))
  rw [map_mul,map_mul,map_star]
lemma conj_duplicate (v : unitary (Mat Q)) (a : Mat P) (b : Mat Q) :
    conj (duplicateUnitary (P:=P) (Q:=Q) (R:=R) v) (sumBlock (a,block (fun _ : R => b))) =
      sumBlock (a,block (fun _ : R => conj v b)) := by
  have hm := map_conj (duplicate (P:=P) (Q:=Q) (R:=R)) (prodUnitary 1 v) (a,b)
  change duplicate (conj (prodUnitary 1 v) (a,b)) = _ at hm
  change conj (Unitary.map (StarMonoidHom.ofClass (duplicate (P:=P) (Q:=Q) (R:=R))) (prodUnitary 1 v))
    (duplicate (a,b)) = _
  rw [← hm]
  change duplicate ((1:Mat P)*a*star (1:Mat P),conj v b)=_
  simp only [star_one,one_mul,mul_one]
  rfl
end KirchbergRordam.EndpointMultiplicity
namespace KirchbergRordam.EndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration
open scoped ComplexOrder CStarAlgebra
variable {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]

variable {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
lemma commutator_approx (ρ : D →⋆ₐ[ℂ] B) (a b : B) (d : D) {ε : ℝ}
    (hc : Commute (ρ d) b) (h : ‖a-b‖≤ε) :
    ‖ρ d*a-a*ρ d‖≤2*ε*‖d‖ := by
  have he : ρ d*a-a*ρ d=ρ d*(a-b)-(a-b)*ρ d := by
    rw [mul_sub,sub_mul,hc.eq]
    abel
  rw [he]
  calc
    _ ≤ ‖ρ d‖*‖a-b‖+‖a-b‖*‖ρ d‖ := (norm_sub_le _ _).trans
      (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖d‖*ε+ε*‖d‖ := add_le_add
      (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ρ d) h (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul h (NonUnitalStarAlgHom.norm_apply_le ρ d) (norm_nonneg _) (le_trans (norm_nonneg _) h))
    _ = _ := by ring
lemma duplicate_difference (a : Mat P) (x y : Mat Q) :
    ‖sumBlock (a,block (fun _ : R => x))-sumBlock (a,block (fun _ : R => y))‖≤‖x-y‖ := by
  change ‖duplicate (a,x)-duplicate (a,y)‖≤_
  rw [←map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le (duplicate (P:=P) (Q:=Q) (R:=R)) _).trans
    (by simp [Prod.norm_def])
end KirchbergRordam.EndpointMultiplicity
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MultiplicativeChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.DropChannels
open MatrixDiagonalPath DiagonalIteration
open MultiplicativeChannel (Channel weighted restrictDrop)
open scoped CStarAlgebra ComplexOrder
variable {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable (p q : ℕ)
variable (w : unitInterval → unitary (PrimeDimensionDrop.Fiber p q)) (hw : Continuous w)
lemma unit_sum (h0 : w 0=1) (ρ : D →⋆ₐ[ℂ] Mat (Fin p))
    (v : unitInterval → unitary (PrimeDimensionDrop.Fiber p q)) (hv : Continuous v)
    (h1 : v 1=1) (σ : D →⋆ₐ[ℂ] Mat (Fin q)) :
    left p q w hw h0 ρ 1+right p q v hv h1 σ 1=1 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change leftScalar t • conj (w t) (MatrixTensor.leftMatrix (ρ 1))+
    rightScalar t • conj (v t) (MatrixTensor.rightMatrix (σ 1))=1
  rw [map_one,map_one,map_one,map_one,map_one,map_one,←add_smul]
  have he : leftScalar t+rightScalar t=1 := by simp [leftScalar,rightScalar]
  rw [he,one_smul]

variable {p q w hw}
lemma norm_conjugate_commutator (u : unitary B) (r a : B) :
    ‖conj u r*a-a*conj u r‖=‖r*conj (star u) a-conj (star u) a*r‖ := by
  rw [←StarAlgEquiv.norm_map (conj (star u)) (conj u r*a-a*conj u r)]
  rw [map_sub,map_mul,map_mul,conj_star]
lemma norm_commutator_change (r x a : B) :
    ‖r*x-x*r‖≤‖r*a-a*r‖+2*‖x-a‖*‖r‖ := by
  have he : r*x-x*r=(r*a-a*r)+(r*(x-a)-(x-a)*r) := by
    simp only [mul_sub,sub_mul]; abel
  rw [he]
  calc
    _ ≤ ‖r*a-a*r‖+(‖r‖*‖x-a‖+‖x-a‖*‖r‖) :=
      (norm_add_le _ _).trans (add_le_add_right
        ((norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) _)
    _ = _ := by ring
lemma smul_commutator (z : ℂ) (r a : B) (hz : ‖z‖≤1) :
    ‖(z • r)*a-a*(z • r)‖≤‖r*a-a*r‖ := by
  rw [smul_mul_assoc,mul_smul_comm,←smul_sub,norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hz
end KirchbergRordam.DropChannels
namespace KirchbergRordam.DropChannels
open DiagonalIteration
open scoped CStarAlgebra ComplexOrder
variable {A B D : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra D]
lemma commutator_map_bound (φ : A →⋆ₐ[ℂ] B) (r a : A) :
    ‖φ r*φ a-φ a*φ r‖≤‖r*a-a*r‖ := by
  rw [←map_mul φ,←map_mul φ,←map_sub φ]
  exact NonUnitalStarAlgHom.norm_apply_le φ _
lemma norm_sub_conj (u : unitary A) (a b : A) :
    ‖a-conj u b‖=‖conj (star u) a-b‖ := by
  rw [←StarAlgEquiv.norm_map (conj (star u)) (a-conj u b),map_sub,conj_star]
lemma transport_bound (ρ : D →⋆ₐ[ℂ] A) (d : D) (u : unitary A) (a b : A)
    {ε δ : ℝ} (hε : 0≤ε) (hv : ‖conj (star u) a-b‖≤ε)
    (hb : ‖ρ d*b-b*ρ d‖≤δ*‖d‖) :
    ‖conj u (ρ d)*a-a*conj u (ρ d)‖≤(δ+2*ε)*‖d‖ := by
  rw [norm_conjugate_commutator]
  calc
    _ ≤ ‖ρ d*b-b*ρ d‖+2*‖conj (star u) a-b‖*‖ρ d‖ := norm_commutator_change _ _ _
    _ ≤ δ*‖d‖+2*ε*‖d‖ := add_le_add hb
      (mul_le_mul (mul_le_mul_of_nonneg_left hv (by norm_num))
        (NonUnitalStarAlgHom.norm_apply_le ρ d) (norm_nonneg _) (by positivity))
    _ = _ := by ring
end KirchbergRordam.DropChannels

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_GeneralSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GeneralBlockReindex
open MatrixBlockReindex MatrixDiagonalPath

open scoped CStarAlgebra Matrix
variable {P Q L R S T U : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]
lemma left_entry (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
    (a : Mat P) (m : Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
    block (Sum.elim (fun _ : L => MatrixTensor.leftMatrix (κ:=Q) a) (fun _ : R => m)) x y =
      MatrixTensor.leftMatrix (sumBlock (block (fun _ : U => a),block (fun _ : S => m)))
        (repackLeft hL hR x) (repackLeft hL hR y) := by
  rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
  · by_cases he : (j,l)=(j',l')
    · cases he; simp [block_apply]
    · have hh : (hL (j,l)).1≠(hL (j',l')).1 ∨ (hL (j,l)).2≠(hL (j',l')).2 := by
        by_contra h; push Not at h; exact he (hL.injective (Prod.ext h.1 h.2))
      have hjl : j≠j' ∨ l≠l' := by simpa only [Prod.mk.injEq,not_and_or] using he
      rcases hh with h|h <;> rcases hjl with hjl|hjl <;>
        simp [block_apply,h,hjl]
  · simp [block_apply]
  · simp [block_apply]
  · by_cases hr : r=r'
    · subst r'; simp [block_apply]
    · have hrr : (hR r).1≠(hR r').1 ∨ (hR r).2≠(hR r').2 := by
        by_contra h; push Not at h; exact hr (hR.injective (Prod.ext h.1 h.2))
      rcases hrr with h|h <;> simp [block_apply,hr,h]
lemma left_matrix (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
    (a : Mat P) (m : Mat (P×Q)) :
    CStarMatrix.reindexₐ ℂ ℂ (repackLeft hL hR)
      (block (Sum.elim (fun _ : L => MatrixTensor.leftMatrix (κ:=Q) a) (fun _ : R => m))) =
        MatrixTensor.leftMatrix (sumBlock (block (fun _ : U => a),block (fun _ : S => m))) := by
  ext x y
  exact left_entry hL hR a m ((repackLeft hL hR).symm x)
    ((repackLeft hL hR).symm y) |>.trans (by simp)
end KirchbergRordam.GeneralBlockReindex
namespace KirchbergRordam.GeneralDropSystem
open MatrixDiagonalPath MatrixBlockReindex
open BalancedDropSystem (half lowerPath upperPath lower_zero lower_one upper_zero upper_one)
open scoped CStarAlgebra Matrix ComplexOrder

variable {p q P Q : ℕ} (d : Data p q P Q)
lemma eigen_lipschitz (i : Slot d) : LipschitzWith (1/2) (eigenpath d i) := by
  rcases i with i|i|i
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    change |(s:ℝ)/2-(t:ℝ)/2|≤(1/2:ℝ)*|(s:ℝ)-(t:ℝ)|
    rw [←sub_div,abs_div]
    norm_num
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    change |((s:ℝ)+1)/2-((t:ℝ)+1)/2|≤(1/2:ℝ)*|(s:ℝ)-(t:ℝ)|
    rw [←sub_div,add_sub_add_right_eq_sub,abs_div]
    norm_num
    linarith
  · exact (LipschitzWith.const _).weaken (by norm_num)
lemma zero_eval (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (a : Mat (Fin p)) (ha : MatrixTensor.leftMatrix a=f 0) :
    evaluationBlock (eigenpath d) 0 f =
      block (Sum.elim (fun _ : Low d => MatrixTensor.leftMatrix (κ:=Fin q) a)
        (fun _ : High d ⊕ Mid d => f half)) := by
  apply congrArg block
  funext k
  rcases k with k|k|k <;> simp [eigenpath,ha]
lemma rawStep_zero (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (a : Mat (Fin p)) (ha : MatrixTensor.leftMatrix a=f 0) :
    rawStep d f 0=MatrixTensor.leftMatrix (κ:=Fin Q)
      (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter d)
        (sumBlock (block (fun _ : Fin d.zeroEnd => a),block (fun _ : Fin d.zeroMid => f half)))) := by
  rw [rawStep_apply,interpolate_zero,zero_eval d f a ha]
  unfold zeroReindex
  rw [reindex_trans,GeneralBlockReindex.left_matrix,reindex_left]
end KirchbergRordam.GeneralDropSystem
namespace KirchbergRordam.GeneralEndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration EndpointMultiplicity
open scoped ComplexOrder CStarAlgebra
variable {P Q R E : Type*} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeR : Fintype R] [Fintype E]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqR : DecidableEq R] [DecidableEq E]
lemma leftExpand_matrix (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (leftExpand (Q:=Q) (R:=R) (E:=E))
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,
        block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a))) =
      MatrixTensor.leftMatrix (κ:=E ⊕ (Q×R)) a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  rcases k with u|⟨b,r⟩ <;> rcases l with v|⟨c,s⟩
  · change a i j*(if u=v then 1 else 0)=a i j*(if (Sum.inl u : E ⊕ Q×R)=.inl v then 1 else 0)
    simp
  · change 0=a i j*0; simp
  · change 0=a i j*0; simp
  · change (if r=s then a i j * (if b=c then 1 else 0) else 0) =
      a i j * (if (Sum.inr (b,r) : E ⊕ Q×R)=.inr (c,s) then 1 else 0)
    by_cases hb : b=c <;> by_cases hr : r=s <;> simp [hb,hr,Prod.ext_iff]
lemma leftBase_commute (h : 2≤Fintype.card (E ⊕ (Q×R))) (a : Mat P)
    (d : DimensionDrop23) :
    Commute (leftBase (P:=P) h d)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a))) := by
  let e := CStarMatrix.reindexₐ ℂ ℂ (leftExpand (P:=P) (Q:=Q) (R:=R) (E:=E))
  apply e.injective
  change e (leftBase h d * _)=e (_ * leftBase h d)
  rw [map_mul,map_mul,leftExpand_matrix]
  have he : e (leftBase (P:=P) h d)=MatrixTensor.rightMatrix
      (DropMatrixRepresentations.representation _ h d) := by
    simp only [leftBase,StarAlgHom.comp_apply,
      CStarMatrix.reindexₐ_symm]
    change e (e.symm (MatrixTensor.rightMatrix (DropMatrixRepresentations.representation _ h d))) = _
    exact e.apply_symm_apply _
  rw [he]
  exact (MatrixTensor.legs_commute a _).symm.eq
lemma leftRep_commute (h : 2≤Fintype.card (E ⊕ (Q×R))) (v : unitary (Mat (P×Q)))
    (a : Mat P) (d : DimensionDrop23) :
    Commute (leftRep h v d)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => conj v (MatrixTensor.leftMatrix (κ:=Q) a)))) := by
  have hc := (leftBase_commute h a d).map
    (conj (duplicateUnitary (P:=P×E) (Q:=P×Q) (R:=R) v)).toRingHom
  change Commute (conj (duplicateUnitary (P:=P×E) (Q:=P×Q) (R:=R) v) (leftBase h d))
    (conj (duplicateUnitary (P:=P×E) (Q:=P×Q) (R:=R) v)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a)))) at hc
  rw [conj_duplicate] at hc
  exact hc

lemma leftRep_bound (h : 2≤Fintype.card (E ⊕ (Q×R))) (v : unitary (Mat (P×Q)))
    (a : Mat P) (x : Mat (P×Q)) (d : DimensionDrop23) {ε : ℝ}
    (hx : ‖x-conj v (MatrixTensor.leftMatrix (κ:=Q) a)‖≤ε) :
    ‖leftRep h v d*sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => x))-
      sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => x))*leftRep h v d‖≤2*ε*‖d‖ :=
  commutator_approx (leftRep h v) _ _ d (leftRep_commute h v a d)
    ((duplicate_difference (MatrixTensor.leftMatrix (κ:=E) a) x _).trans hx)
end KirchbergRordam.GeneralEndpointMultiplicity
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
lemma size_two (n : ℕ) : 2≤S.size n := by
  rw [S.size_power]
  exact Nat.le_self_pow (by omega) 2
instance instNeZeroNatSize (n : ℕ) : NeZero (S.size n) := ⟨by have := S.size_two n; omega⟩
instance instNontrivialStage (n : ℕ) : Nontrivial (S.Stage n) := inferInstanceAs
  (Nontrivial (PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)))

instance instNontrivialObjSystem (n : ℕ) : Nontrivial (S.system.obj n) := inferInstanceAs (Nontrivial (S.Stage n))
instance instSeparableSpaceAlgebra : TopologicalSpace.SeparableSpace S.Algebra := inferInstanceAs (TopologicalSpace.SeparableSpace (CStarInductiveLimit.Algebra S.system))
lemma inclusion_map (i j : ℕ) (hij : i≤j) (x : S.Stage i) :
    S.inclusion j (S.chain.map i j hij x)=S.inclusion i x := CStarInductiveLimit.of_map _ _ _ _ _
end KirchbergRordam.PrimeDropPresentation
namespace KirchbergRordam.PrimeDropPresentation.Iteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open MatrixDiagonalPath DiagonalIteration GeneralDropSystem
variable (S : PrimeDropPresentation)

lemma eigen_lipschitz : ∀ n i, LipschitzWith (1/2) ((diagonalSystem S).eigen n i) :=
  fun n i => GeneralDropSystem.eigen_lipschitz (S.stepData n) i

lemma iterate_full (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    (S.chain.map n (n+k) (Nat.le_add_right n k) f).val t =
      (diagonalSystem S).full n k f.val t := by
  induction k generalizing t with
  | zero => simp only [Nat.add_zero,S.chain.map_self,DiagonalIteration.System.full]; rfl
  | succ k ih =>
    erw [S.chain.map_succ n (n+k) (Nat.le_add_right n k)]
    change MatrixDiagonalPath.interpolate _ _ t
      (block (fun i => (S.chain.map n (n+k) _ f).val (eigenpath (S.stepData (n+k)) i t))) = _
    simp only [ih]
    rfl

lemma untwist (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    conj (star (normalizedPath S n k t))
      ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t) =
      conj ((diagonalSystem S).unitaryPath n k 0) ((diagonalSystem S).flat n k f.val t) := by
  rw [iterate_full S,(diagonalSystem S).full_eq]
  exact DiagonalIteration.normalize_cancel _ _ _

lemma untwist_norm (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    ‖conj (star (normalizedPath S n k t))
      ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
      (S.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖ =
      ‖(diagonalSystem S).flat n k f.val t-(diagonalSystem S).flat n k f.val 0‖ := by
  rw [untwist S,iterate_full S,(diagonalSystem S).full_eq]
  rw [←map_sub,StarAlgEquiv.norm_map]

lemma eventually_untwist_small (n : ℕ) (f : S.Stage n) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖≤ε := by
  filter_upwards [(diagonalSystem S).flat_eventually_small (eigen_lipschitz S) n f.val ε hε] with k hk t
  rw [untwist_norm S]
  exact hk t 0
end KirchbergRordam.PrimeDropPresentation.Iteration
namespace KirchbergRordam.PrimeDropPresentation.HalfFlip
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open PrimeDropPresentation.Iteration
open UnitaryDisplacement BalancedDropHalfFlip
variable (S : PrimeDropPresentation)

lemma common_stage (F : Finset S.Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, ∃ a : S.Algebra → S.Stage n, ∀ x∈F, ‖S.inclusion n (a x)-x‖<ε :=
  CStarInductiveLimit.approximation_common_stage S.system F ε hε

end KirchbergRordam.PrimeDropPresentation.HalfFlip
namespace KirchbergRordam.PrimeDropPresentation.Channels
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration GeneralEndpointMultiplicity
open DropMatrixRepresentations DropChannels GeneralDropSystem
open BalancedDropSystem (half)
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
lemma block_const_left {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P] [DecidableEq E]
    (a : Mat P) : block (fun _ : E => a)=MatrixTensor.leftMatrix (κ:=E) a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  change (if k=l then a i j else 0)=a i j*(if k=l then 1 else 0)
  split <;> simp_all

lemma zeroRep_bound (n : ℕ)
    (v : unitary (PrimeDimensionDrop.Fiber (S.size n) (S.size n+1)))
    (f : S.Stage n) (d : DimensionDrop23) {ε : ℝ}
    (hf : ‖conj (star v) (f.val half)-f.val 0‖≤ε) :
    ‖MatrixTensor.leftMatrix (κ:=Fin (S.size (n+1)+1)) (zeroRep S n v d)*(step (S.stepData n) f).val 0-
      (step (S.stepData n) f).val 0*MatrixTensor.leftMatrix (κ:=Fin (S.size (n+1)+1)) (zeroRep S n v d)‖≤2*ε*‖d‖ := by
  have he := rawStep_zero (S.stepData n) f.val _ (leftValue_spec (S.size n) (S.size n+1) f)
  change (step (S.stepData n) f).val 0=_ at he
  rw [block_const_left] at he
  rw [he]
  let φ := (MatrixTensor.leftMatrix (κ:=Fin (S.size (n+1)+1))).comp
    (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter (S.stepData n))).toStarAlgHom
  apply (commutator_map_bound φ _ _).trans
  apply leftRep_bound (zeroCount S n)
  erw [leftValue_spec (S.size n) (S.size n+1) f]
  rw [norm_sub_conj]
  exact hf
end KirchbergRordam.PrimeDropPresentation.Channels
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation.Channels
open MatrixDiagonalPath DiagonalIteration PrimeDropPresentation.Iteration
open GeneralDropSystem DropChannels
open BalancedDropSystem (half)
variable (S : PrimeDropPresentation)
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology

lemma stage_unit_sum (n k : ℕ) : stageLeft S n k 1+stageRight S n k 1=1 :=
  DropChannels.unit_sum _ _ _ _ _ _ _ _ _ _
lemma map_next (n k : ℕ) (x : S.Stage n) :
    S.chain.map n (n+k+1) (by omega) x =
      step (S.stepData (n+k))
        (S.chain.map n (n+k) (Nat.le_add_right n k) x) := by
  rw [S.chain.map_succ n (n+k) (Nat.le_add_right n k)]
  rfl
lemma stageLeft_bound (n k : ℕ) (x : S.Stage n) {ε : ℝ} (hε : 0≤ε)
    (hp : ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε)
    (hf : ∀ t : unitInterval,
      ‖conj (star (finalPath S n k t))
        ((S.chain.map n (n+k+1) (by omega) x).val t)-
        (S.chain.map n (n+k+1) (by omega) x).val 0‖≤ε)
    (d : DimensionDrop23) :
    ‖stageLeft S n k d * (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x)-
      (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x) * stageLeft S n k d‖≤4*ε*‖d‖ := by
  let g : S.Stage (n+k+1) := S.chain.map n (n+k+1) (by omega) x
  change ‖((stageLeft S n k d*g-g*stageLeft S n k d).val)‖≤_
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(leftScalar t • conj (finalPath S n k t)
      (MatrixTensor.leftMatrix (zeroRep S (n+k) (normalizedPath S n k half) d))) * g.val t-
    g.val t*(leftScalar t • conj (finalPath S n k t)
      (MatrixTensor.leftMatrix (zeroRep S (n+k) (normalizedPath S n k half) d)))‖≤_
  apply (smul_commutator _ _ _ (leftScalar_norm t)).trans
  let ρ : DimensionDrop23 →⋆ₐ[ℂ] MatrixTensor.Mat (Fin (S.size (n+k+1)) × Fin (S.size (n+k+1)+1)) := MatrixTensor.leftMatrix.comp
    (zeroRep S (n+k) (normalizedPath S n k half))
  have he := zeroRep_bound S (n+k) (normalizedPath S n k half)
    (S.chain.map n (n+k) (Nat.le_add_right n k) x) d (hp half)
  rw [←map_next S n k x] at he
  have ht := transport_bound ρ d (finalPath S n k t) (g.val t) (g.val 0) hε (hf t) he
  convert ht using 1 <;> first | rfl | ring
end KirchbergRordam.PrimeDropPresentation.Channels
namespace KirchbergRordam.PrimeDropPresentation.Channels
open PrimeDropPresentation.Iteration
variable (S : PrimeDropPresentation)
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology
lemma finite_stage (n : ℕ) (F : Finset (S.Stage n)) (ε : ℝ) (hε : 0<ε) :
    ∃ φ ψ : Channel DimensionDrop23 S.Algebra, φ 1+ψ 1=1 ∧
      ∀ x∈F, ∀ d : DimensionDrop23,
        ‖φ d*S.inclusion n x-S.inclusion n x*φ d‖≤ε*‖d‖ ∧
        ‖ψ d*S.inclusion n x-S.inclusion n x*ψ d‖≤ε*‖d‖ := by
  have he : ∀ᶠ k in atTop, ∀ x∈F, ∀ t : unitInterval,
      ‖DiagonalIteration.conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε/8 := by
    apply (Filter.eventually_all_finset F).mpr
    intro x hx
    exact eventually_untwist_small S n x (ε/8) (by positivity)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp he
  let φ := MultiplicativeChannel.postcompose (stageLeft S n K) (S.inclusion (n+K+1))
  let ψ := MultiplicativeChannel.postcompose (stageRight S n K) (S.inclusion (n+K+1))
  refine ⟨φ,ψ,?_,fun x hx d => ?_⟩
  · change S.inclusion _ (stageLeft S n K 1)+S.inclusion _ (stageRight S n K 1)=1
    rw [←map_add,stage_unit_sum S,map_one]
  · have hl := stageLeft_bound S n K x (by positivity : 0≤ε/8) (hK K le_rfl x hx)
      (hK (K+1) (Nat.le_succ K) x hx) d
    have hr := stageRight_bound S n K x (by positivity : 0≤ε/8) (hK K le_rfl x hx)
      (hK (K+1) (Nat.le_succ K) x hx) d
    have hm : S.inclusion (n+K+1) (S.chain.map n (n+K+1) (by omega) x)=S.inclusion n x :=
      S.inclusion_map n (n+K+1) (by omega) x
    have hc (r : S.Stage (n+K+1)) := DropChannels.commutator_map_bound
      (S.inclusion (n+K+1)) r (S.chain.map n (n+K+1) (by omega) x)
    have hcl := (hc (stageLeft S n K d)).trans hl
    have hcr := (hc (stageRight S n K d)).trans hr
    rw [hm] at hcl hcr
    change _≤_ at hcl
    refine ⟨hcl.trans ?_,hcr.trans ?_⟩ <;> nlinarith [norm_nonneg d]

lemma channel_perturbation (φ : Channel DimensionDrop23 S.Algebra) (d : DimensionDrop23)
    (x y : S.Algebra) :
    ‖φ d*x-x*φ d‖≤‖φ d*y-y*φ d‖+2*‖x-y‖*‖d‖ := by
  calc
    _ ≤ ‖φ d*y-y*φ d‖+2*‖x-y‖*‖φ d‖ := DropChannels.norm_commutator_change (φ d) x y
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (φ.norm_le d)
      (by positivity : 0≤2*‖x-y‖))

lemma finite_control_oai (F : Finset S.Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ φ ψ : Channel DimensionDrop23 S.Algebra, φ 1+ψ 1=1 ∧
      ∀ x∈F, ∀ d : DimensionDrop23,
        ‖φ d*x-x*φ d‖≤ε*‖d‖ ∧ ‖ψ d*x-x*ψ d‖≤ε*‖d‖ := by
  classical
  obtain ⟨n,a,ha⟩ := PrimeDropPresentation.HalfFlip.common_stage S F (ε/4) (by positivity)
  obtain ⟨φ,ψ,hu,h⟩ := finite_stage S n (F.image a) (ε/2) (by positivity)
  refine ⟨φ,ψ,hu,fun x hx d => ?_⟩
  have hb := h (a x) (Finset.mem_image_of_mem a hx) d
  have hd := (ha x hx).le
  rw [norm_sub_rev] at hd
  constructor
  · have hc := channel_perturbation S φ d x (S.inclusion n (a x))
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg d),hb.1]
  · have hc := channel_perturbation S ψ d x (S.inclusion n (a x))
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg d),hb.2]
end KirchbergRordam.PrimeDropPresentation.Channels
end

end OAI
end

theorem solution : type_of% @OAI.KirchbergRordam.PrimeDropPresentation.Channels.finite_control_oai := @OAI.KirchbergRordam.PrimeDropPresentation.Channels.finite_control_oai
