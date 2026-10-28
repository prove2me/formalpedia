-- Prove2me | solution 1 for OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:40:17.461588+00:00
-- url     : https://prove2.me/submissions/f80ac090-8cf4-4462-9664-6cf9e64f48dd

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr015

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

namespace KirchbergRordam.MatrixPermutationPath
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma perm_conjugation (σ : Equiv.Perm ι) (a : Mat ι) :
    Unitary.conjStarAlgAut ℂ _ (perm σ) a = CStarMatrix.reindexₐ ℂ ℂ σ a := by
  change σ⁻¹.permMatrix ℂ * CStarMatrix.ofMatrix.symm a * (σ⁻¹.permMatrix ℂ)ᴴ =
    Matrix.reindex σ σ (CStarMatrix.ofMatrix.symm a)
  rw [Matrix.conjTranspose_permMatrix]
  change σ.symm.toPEquiv.toMatrix * CStarMatrix.ofMatrix.symm a * σ.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl


end KirchbergRordam.MatrixPermutationPath

namespace KirchbergRordam.MatrixDiagonalPath
open scoped ComplexOrder CStarAlgebra Matrix
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [instDecidableEqκ : DecidableEq κ] [Fintype ν] [DecidableEq ν]


omit instDecidableEqκ in
lemma interpolate_one.{contextLevel1, contextLevel2}
    {κ : Type contextLevel1}
    {ν : Type contextLevel2}
    [Fintype κ]
    [DecidableEq κ]
    [Fintype ν]
    [DecidableEq ν]
    (e₀ e₁ : κ ≃ ν) (a : Mat κ) :
    interpolate e₀ e₁ 1 a = CStarMatrix.reindexₐ ℂ ℂ e₁ a := by
  simp only [interpolate, StarAlgEquiv.trans_apply, Path.target,
    MatrixPermutationPath.perm_conjugation]
  ext i j
  change a (e₀.symm ((e₀.symm.trans e₁).symm i))
    (e₀.symm ((e₀.symm.trans e₁).symm j)) = a (e₁.symm i) (e₁.symm j)
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
lemma reindex_block (e : P ≃ Q) (a : P → Mat R) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl R) e) (block a) =
      block (fun i => a (e.symm i)) := by
  ext i j
  rcases i with ⟨r,p⟩; rcases j with ⟨s,q⟩
  change (if e.symm p=e.symm q then a (e.symm p) r s else 0) =
    (if p=q then a (e.symm p) r s else 0)
  simp only [e.symm.injective.eq_iff]
lemma reindex_right (e : P ≃ Q) (f : R ≃ S) (a : Mat R) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (_root_.OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι:=P) a) =
      _root_.OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι:=Q) (CStarMatrix.reindexₐ ℂ ℂ f a) := by
  ext i j
  rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
  change _root_.OAI.KirchbergRordam.MatrixTensor.rightMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
  simp only [right_apply, e.symm.injective.eq_iff]
  rfl
end KirchbergRordam.MatrixBlockReindex


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DiagonalIteration
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
attribute [instance] System.cstar System.finite
end KirchbergRordam.DiagonalIteration
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
lemma norm_twisted_difference (u v : unitary A) (a b : A) :
    ‖conj (star (u*star v)) a-b‖=‖conj (star u) a-conj (star v) b‖ := by
  have hb : conj v (conj (star v) b)=b := by simpa only [star_star] using conj_star (star v) b
  calc
    _ = ‖conj v (conj (star u) a-conj (star v) b)‖ := by
      rw [map_sub,hb,star_mul,star_star,DiagonalIteration.conj_mul]
    _ = _ := StarAlgEquiv.norm_map _ _
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
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedChannels
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

namespace KirchbergRordam.BalancedDropChannels
open MatrixDiagonalPath DiagonalIteration
open BalancedDropSystem DropChannels
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology

lemma norm_sub_two {B : Type*} [SeminormedAddCommGroup B] (a b c : B) {ε : ℝ}
    (ha : ‖a-c‖≤ε) (hb : ‖b-c‖≤ε) : ‖a-b‖≤2*ε := by
  calc
    _ = ‖(a-c)-(b-c)‖ := by congr 1; abel
    _ ≤ ‖a-c‖+‖b-c‖ := norm_sub_le _ _
    _ ≤ _ := by linarith
end KirchbergRordam.BalancedDropChannels
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
lemma right_entry (hL : P × L ≃ T × U) (hR : R ≃ T × S)
    (a : Mat Q) (m : Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
    block (Sum.elim (fun _ : L => MatrixTensor.rightMatrix (ι:=P) a) (fun _ : R => m)) x y =
      MatrixTensor.rightMatrix (sumBlock (block (fun _ : U => a),block (fun _ : S => m)))
        (repackRight hL hR x) (repackRight hL hR y) := by
  rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
  · by_cases he : (i,l)=(i',l')
    · cases he; simp [block_apply]
    · have hh : (hL (i,l)).1≠(hL (i',l')).1 ∨ (hL (i,l)).2≠(hL (i',l')).2 := by
        by_contra h; push Not at h; exact he (hL.injective (Prod.ext h.1 h.2))
      have hil : i≠i' ∨ l≠l' := by simpa only [Prod.mk.injEq,not_and_or] using he
      rcases hh with h|h <;> rcases hil with hil|hil <;>
        simp [block_apply,h,hil]
  · simp [block_apply]
  · simp [block_apply]
  · by_cases hr : r=r'
    · subst r'; simp [block_apply]
    · have hrr : (hR r).1≠(hR r').1 ∨ (hR r).2≠(hR r').2 := by
        by_contra h; push Not at h; exact hr (hR.injective (Prod.ext h.1 h.2))
      rcases hrr with h|h <;> simp [block_apply,hr,h]
lemma right_matrix (hL : P × L ≃ T × U) (hR : R ≃ T × S)
    (a : Mat Q) (m : Mat (P×Q)) :
    CStarMatrix.reindexₐ ℂ ℂ (repackRight hL hR)
      (block (Sum.elim (fun _ : L => MatrixTensor.rightMatrix (ι:=P) a) (fun _ : R => m))) =
        MatrixTensor.rightMatrix (sumBlock (block (fun _ : U => a),block (fun _ : S => m))) := by
  ext x y
  exact right_entry hL hR a m ((repackRight hL hR).symm x)
    ((repackRight hL hR).symm y) |>.trans (by simp)
end KirchbergRordam.GeneralBlockReindex
namespace KirchbergRordam.GeneralDropSystem
open MatrixDiagonalPath MatrixBlockReindex
open BalancedDropSystem (half lowerPath upperPath lower_zero lower_one upper_zero upper_one)
open scoped CStarAlgebra Matrix ComplexOrder

variable {p q P Q : ℕ} (d : Data p q P Q)
lemma one_eval (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (b : Mat (Fin q)) (hb : MatrixTensor.rightMatrix b=f 1) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl (Fin p × Fin q)) (slotSwap d))
      (evaluationBlock (eigenpath d) 1 f)=
      block (Sum.elim (fun _ : High d => MatrixTensor.rightMatrix (ι:=Fin p) b)
        (fun _ : Low d ⊕ Mid d => f half)) := by
  change CStarMatrix.reindexₐ ℂ ℂ _ (block _) = _
  rw [reindex_block]
  apply congrArg block
  funext k
  rcases k with k|k|k <;> simp [slotSwap,eigenpath,hb]
lemma rawStep_one (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (b : Mat (Fin q)) (hb : MatrixTensor.rightMatrix b=f 1) :
    rawStep d f 1=MatrixTensor.rightMatrix (ι:=Fin P)
      (CStarMatrix.reindexₐ ℂ ℂ (oneOuter d)
        (sumBlock (block (fun _ : Fin d.oneEnd => b),block (fun _ : Fin d.oneMid => f half)))) := by
  rw [rawStep_apply,interpolate_one]
  unfold oneReindex
  rw [reindex_trans,one_eval d f b hb,reindex_trans,GeneralBlockReindex.right_matrix,reindex_right]

end KirchbergRordam.GeneralDropSystem
namespace KirchbergRordam.GeneralEndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration EndpointMultiplicity
open scoped ComplexOrder CStarAlgebra
variable {P Q R E : Type*} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeR : Fintype R] [Fintype E]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqR : DecidableEq R] [DecidableEq E]
lemma rightExpand_matrix (a : Mat Q) :
    CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (R:=R) (E:=E))
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,
        block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a))) =
      MatrixTensor.leftMatrix (κ:=E ⊕ (P×R)) a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  rcases k with u|⟨b,r⟩ <;> rcases l with v|⟨c,s⟩
  · change a i j*(if u=v then 1 else 0)=a i j*(if (Sum.inl u : E ⊕ P×R)=.inl v then 1 else 0)
    simp
  · change 0=a i j*0; simp
  · change 0=a i j*0; simp
  · change (if r=s then (if b=c then 1 else 0) * a i j else 0) =
      a i j * (if (Sum.inr (b,r) : E ⊕ P×R)=.inr (c,s) then 1 else 0)
    by_cases hb : b=c <;> by_cases hr : r=s <;> simp [hb,hr,Prod.ext_iff]
lemma rightBase_commute (h : 2≤Fintype.card (E ⊕ (P×R))) (a : Mat Q)
    (d : DimensionDrop23) :
    Commute (rightBase (Q:=Q) h d)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a))) := by
  let e := CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (Q:=Q) (R:=R) (E:=E))
  apply e.injective
  change e (rightBase h d * _)=e (_ * rightBase h d)
  rw [map_mul,map_mul,rightExpand_matrix]
  have he : e (rightBase (Q:=Q) h d)=MatrixTensor.rightMatrix
      (DropMatrixRepresentations.representation _ h d) := by
    simp only [rightBase,StarAlgHom.comp_apply,
      CStarMatrix.reindexₐ_symm]
    change e (e.symm (MatrixTensor.rightMatrix (DropMatrixRepresentations.representation _ h d))) = _
    exact e.apply_symm_apply _
  rw [he]
  exact (MatrixTensor.legs_commute a _).symm.eq

lemma rightRep_commute (h : 2≤Fintype.card (E ⊕ (P×R))) (v : unitary (Mat (P×Q)))
    (a : Mat Q) (d : DimensionDrop23) :
    Commute (rightRep h v d)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => conj v (MatrixTensor.rightMatrix (ι:=P) a)))) := by
  have hc := (rightBase_commute h a d).map
    (conj (duplicateUnitary (P:=Q×E) (Q:=P×Q) (R:=R) v)).toRingHom
  change Commute (conj (duplicateUnitary (P:=Q×E) (Q:=P×Q) (R:=R) v) (rightBase h d))
    (conj (duplicateUnitary (P:=Q×E) (Q:=P×Q) (R:=R) v)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a)))) at hc
  rw [conj_duplicate] at hc
  exact hc

lemma rightRep_bound (h : 2≤Fintype.card (E ⊕ (P×R))) (v : unitary (Mat (P×Q)))
    (a : Mat Q) (x : Mat (P×Q)) (d : DimensionDrop23) {ε : ℝ}
    (hx : ‖x-conj v (MatrixTensor.rightMatrix (ι:=P) a)‖≤ε) :
    ‖rightRep h v d*sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => x))-
      sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => x))*rightRep h v d‖≤2*ε*‖d‖ :=
  commutator_approx (rightRep h v) _ _ d (rightRep_commute h v a d)
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
end KirchbergRordam.PrimeDropPresentation
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

lemma oneRep_bound (n : ℕ)
    (v : unitary (PrimeDimensionDrop.Fiber (S.size n) (S.size n+1)))
    (f : S.Stage n) (d : DimensionDrop23) {ε : ℝ}
    (hf : ‖conj (star v) (f.val half)-f.val 1‖≤ε) :
    ‖MatrixTensor.rightMatrix (ι:=Fin (S.size (n+1))) (oneRep S n v d)*(step (S.stepData n) f).val 1-
      (step (S.stepData n) f).val 1*MatrixTensor.rightMatrix (ι:=Fin (S.size (n+1))) (oneRep S n v d)‖≤2*ε*‖d‖ := by
  have he := rawStep_one (S.stepData n) f.val _ (rightValue_spec (S.size n) (S.size n+1) f)
  change (step (S.stepData n) f).val 1=_ at he
  rw [block_const_left] at he
  rw [he]
  let φ := (MatrixTensor.rightMatrix (ι:=Fin (S.size (n+1)))).comp
    (CStarMatrix.reindexₐ ℂ ℂ (oneOuter (S.stepData n))).toStarAlgHom
  apply (commutator_map_bound φ _ _).trans
  apply rightRep_bound (oneCount S n)
  erw [rightValue_spec (S.size n) (S.size n+1) f]
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

lemma map_next (n k : ℕ) (x : S.Stage n) :
    S.chain.map n (n+k+1) (by omega) x =
      step (S.stepData (n+k))
        (S.chain.map n (n+k) (Nat.le_add_right n k) x) := by
  rw [S.chain.map_succ n (n+k) (Nat.le_add_right n k)]
  rfl
lemma stageRight_bound_oai (n k : ℕ) (x : S.Stage n) {ε : ℝ} (hε : 0≤ε)
    (hp : ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε)
    (hf : ∀ t : unitInterval,
      ‖conj (star (finalPath S n k t))
        ((S.chain.map n (n+k+1) (by omega) x).val t)-
        (S.chain.map n (n+k+1) (by omega) x).val 0‖≤ε)
    (d : DimensionDrop23) :
    ‖stageRight S n k d * (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x)-
      (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x) * stageRight S n k d‖≤8*ε*‖d‖ := by
  let f : S.Stage (n+k) := S.chain.map n (n+k) (Nat.le_add_right n k) x
  let g : S.Stage (n+k+1) := S.chain.map n (n+k+1) (by omega) x
  have hm : ‖conj (star (normalizedPath S n k half*star (normalizedPath S n k 1)))
      (f.val half)-f.val 1‖≤2*ε := by
    rw [norm_twisted_difference]
    exact BalancedDropChannels.norm_sub_two _ _ _ (hp half) (hp 1)
  have he := oneRep_bound S (n+k)
    (normalizedPath S n k half*star (normalizedPath S n k 1)) f d hm
  change _ ≤ 2*(2*ε)*‖d‖ at he
  rw [show 2*(2*ε)*‖d‖=(4*ε)*‖d‖ by ring] at he
  dsimp only [f] at he
  rw [←map_next S n k x] at he
  change ‖((stageRight S n k d*g-g*stageRight S n k d).val)‖≤_
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(rightScalar t • conj (endPath S n k t)
      (MatrixTensor.rightMatrix (oneRep S (n+k)
        (normalizedPath S n k half*star (normalizedPath S n k 1)) d))) * g.val t-
    g.val t*(rightScalar t • conj (endPath S n k t)
      (MatrixTensor.rightMatrix (oneRep S (n+k)
        (normalizedPath S n k half*star (normalizedPath S n k 1)) d)))‖≤_
  apply (smul_commutator _ _ _ (rightScalar_norm t)).trans
  let ρ : DimensionDrop23 →⋆ₐ[ℂ] MatrixTensor.Mat (Fin (S.size (n+k+1)) × Fin (S.size (n+k+1)+1)) := MatrixTensor.rightMatrix.comp (oneRep S (n+k)
    (normalizedPath S n k half*star (normalizedPath S n k 1)))
  have ht : ‖conj (star (endPath S n k t)) (g.val t)-g.val 1‖≤2*ε := by
    rw [endPath,norm_twisted_difference]
    exact BalancedDropChannels.norm_sub_two _ _ _ (hf t) (hf 1)
  have hc := transport_bound ρ d (endPath S n k t) (g.val t) (g.val 1) (by positivity : 0≤2*ε) ht he
  convert hc using 1 <;> first | rfl | ring
end KirchbergRordam.PrimeDropPresentation.Channels
end

end OAI
end

theorem solution : type_of% @OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound_oai := @OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound_oai
