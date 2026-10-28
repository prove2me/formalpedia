-- Prove2me | solution 1 for OAI.Kadison.HilbertModuleSB.exists_unitary_of_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:20:27.83286+00:00
-- url     : https://prove2.me/submissions/5ff46b9f-9076-41a7-8310-250313bc4a64

import Mathlib
import Definitions.Def_OAIQ039C037
import Definitions.Def_OAIQ039C041
import Definitions.Def_OAIQ039C051
import Theorems.Thm_OAI_Kadison_BiprodLinkColumn_component_intertwines

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertBiprodProjections
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

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace H] [CompleteSpace G] in
lemma left_commutes (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block S T*left=left*block S T := by
  rw [left,←block_mul,←block_mul]
  simp

lemma inl_adjoint : (inlL (H:=H) (G:=G)).comp inlL.adjoint=left := by
  rw [adjoint_inlL]
  apply ext
  intro x
  rfl

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionShift
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.ProjectionShift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (w p : H →L[ℂ] H)

variable {w p} {e : H →L[ℂ] H}

lemma conjugate_projection (he : IsStarProjection e) (hw : star w*w=e)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqe : q≤e) :
    IsStarProjection (w*q*star w) := by
  have heq : e*q=q := (hq.le_iff_mul_eq_right he).mp hqe
  constructor
  · calc
      _=w*q*(star w*w)*q*star w := by noncomm_ring
      _=w*q*star w := by rw [hw,mul_assoc (w*q) e q,heq,mul_assoc w q q,hq.isIdempotentElem.eq]
  · simp only [star_mul,star_star,hq.isSelfAdjoint.star_eq,IsSelfAdjoint,mul_assoc]

lemma partial_projection_le (he : IsStarProjection e) (hp : IsStarProjection p)
    (hw : star w*w=e) (hwe : w*e=w) (hpw : p*w=0)
    (hbound : p+w*star w≤e) (n : ℕ) :
    IsStarProjection (partialSum w p n) ∧ partialSum w p n≤e := by
  induction n with
  | zero => exact ⟨IsStarProjection.zero _,he.nonneg⟩
  | succ n ih =>
    refine ⟨hp.add (conjugate_projection he hw ih.1 ih.2) ?_,?_⟩
    · rw [←mul_assoc,←mul_assoc,hpw,zero_mul,zero_mul]
    · exact (add_le_add le_rfl (star_right_conjugate_le_conjugate ih.2 w)).trans
        (by simpa only [hwe] using hbound)

lemma partial_mono (hp : IsStarProjection p) : Monotone (partialSum w p) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa only [partialSum,mul_zero,zero_mul,add_zero] using hp.nonneg
  | succ n ih => exact add_le_add le_rfl (star_right_conjugate_le_conjugate ih w)

lemma partial_mem (M : VonNeumannAlgebra H) (hw : w∈M) (hp : p∈M) (n : ℕ) :
    partialSum w p n∈M := by
  induction n with
  | zero => exact M.zero_mem
  | succ n ih => exact M.add_mem hp (M.mul_mem (M.mul_mem hw ih) (M.star_mem' hw))

theorem exists_fixed_projection (M : VonNeumannAlgebra H)
    (he : IsStarProjection e) (hp : IsStarProjection p)
    (hw : star w*w=e) (hwe : w*e=w) (hpw : p*w=0)
    (hbound : p+w*star w≤e) (hwM : w∈M) (hpM : p∈M) :
    ∃ q : H →L[ℂ] H,q∈M ∧ IsStarProjection q ∧ q≤e ∧ q=p+w*q*star w := by
  obtain ⟨q,hqM,hq,hle,hlim,hleast⟩ := ProjectionChains.exists_strong_sup M (partialSum w p)
    (fun n => (partial_projection_le he hp hw hwe hpw hbound n).1)
    (partial_mem M hwM hpM) (partial_mono hp)
  refine ⟨q,hqM,hq,hleast e he (fun n => (partial_projection_le he hp hw hwe hpw hbound n).2),?_⟩
  ext x
  have hs := (hlim x).comp (tendsto_add_atTop_nat 1)
  have hr := (tendsto_const_nhds (x:=p x) (f:=atTop (α:=ℕ))).add (w.continuous.tendsto (q (star w x)) |>.comp (hlim (star w x)))
  have hh : Tendsto (fun n => partialSum w p (n+1) x) atTop (𝓝 ((p+w*q*star w) x)) := by
    simpa only [Function.comp_def,partialSum,add_apply,mul_apply_eq_comp] using hr
  exact tendsto_nhds_unique hs hh

end Kadison.ProjectionShift

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionSchroederBernstein
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem subEquivalent_antisymm (M : VonNeumannAlgebra H)
    {e f : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) (hf : IsStarProjection f)
    (hef : SubEquivalent M e f) (hfe : SubEquivalent M f e) : Equivalent M e f := by
  obtain ⟨u,hu⟩ := hef
  obtain ⟨v,hv⟩ := hfe
  let a := u.val
  let b := v.val
  let w := b*a
  let p := e-v.final
  have hai : star a*a=e := hu
  have hbi : star b*b=f := hv
  have hea : a*e=a := u.mul_source he
  have hfa : f*a=a := u.target_mul hf
  have heb : e*b=b := v.target_mul he
  have hbf : b*f=b := v.mul_source hf
  have hve : v.final*e=v.final := (v.final_projection.le_iff_mul_eq_left he).mp v.target_le
  have hp : IsStarProjection p := v.final_projection.sub_of_mul_eq_left he hve
  have hw : star w*w=e := by
    calc
      _=star a*(star b*b)*a := by simp only [w,star_mul]; noncomm_ring
      _=e := by rw [hbi,mul_assoc,hfa,hai]
  have hwe : w*e=w := by dsimp [w]; rw [mul_assoc,hea]
  have hew : e*w=w := by dsimp [w]; rw [←mul_assoc,heb]
  have hpw : p*w=0 := by
    change (e-v.final)*(b*a)=0
    rw [←mul_assoc,sub_mul,heb]
    have hvb : v.final*b=b := v.final_mul
    rw [hvb,sub_self,zero_mul]
  have hbound : p+w*star w≤e := by
    have hh : w*star w≤v.final := by
      calc
        _=b*u.final*star b := by simp only [w,Link.final,star_mul]; noncomm_ring
        _≤b*f*star b := star_right_conjugate_le_conjugate u.target_le b
        _=v.final := by rw [hbf]; rfl
    exact (add_le_add le_rfl hh).trans_eq (sub_add_cancel e v.final)
  obtain ⟨q,hqM,hq,hqe,hfix⟩ := ProjectionShift.exists_fixed_projection M he hp hw hwe hpw hbound
    (M.mul_mem v.mem u.mem) (M.sub_mem heM (M.mul_mem v.mem (M.star_mem' v.mem)))
  have heq : e*q=q := (hq.le_iff_mul_eq_right he).mp hqe
  have hqe' : q*e=q := (hq.le_iff_mul_eq_left he).mp hqe
  have hpq : p≤q := by
    rw [hfix]
    exact le_add_of_nonneg_right (star_right_conjugate_nonneg hq.nonneg w)
  have hpq' : p*q=p := (hp.le_iff_mul_eq_left hq).mp hpq
  have hqp : q*p=p := (hp.le_iff_mul_eq_right hq).mp hpq
  have hqw : q*w=w*q := by
    calc
      _=(p+w*q*star w)*w := by rw [←hfix]
      _=w*q*(star w*w) := by rw [add_mul,hpw,zero_add]; noncomm_ring
      _=w*q := by rw [hw,mul_assoc,hqe']
  have hcross : (e-q)*w*q=0 := by
    calc
      _=w*q-(w*q)*q := by rw [sub_mul,sub_mul,hew,hqw]
      _=0 := by rw [mul_assoc w q q,hq.isIdempotentElem.eq,sub_self]
  have hcross' : q*star w*(e-q)=0 := by
    simpa only [star_mul,star_sub,he.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq,star_zero,mul_assoc]
      using congrArg star hcross
  have hrem : (e-q)*(b*star b)=e-q := by
    have hb : b*star b=e-p := by dsimp [p,Link.final,b]; noncomm_ring
    rw [hb]
    have hpe : p*e=p := (hp.le_iff_mul_eq_left he).mp (hpq.trans hqe)
    have hep : e*p=p := (hp.le_iff_mul_eq_right he).mp (hpq.trans hqe)
    calc
      _=e*e-e*p-q*e+q*p := by noncomm_ring
      _=e-q := by rw [he.isIdempotentElem.eq,hep,hqe',hqp]; abel
  let r := a*q+star b*(e-q)
  have hri : star r*r=e := by
    have hs : star r=q*star a+(e-q)*b := by
      dsimp [r]
      simp only [star_add,star_mul,star_sub,star_star,hq.isSelfAdjoint.star_eq,he.isSelfAdjoint.star_eq]
    calc
      _=(q*(star a*a)*q)+(q*star w*(e-q))+((e-q)*w*q)+((e-q)*(b*star b)*(e-q)) := by
        rw [hs]; dsimp [r,w]; simp only [star_mul]; noncomm_ring
      _=q+(e-q)*(e-q) := by
        rw [hai,mul_assoc q e q,heq,hq.isIdempotentElem.eq,hcross',hcross,hrem,add_zero,add_zero]
      _=e := by
        have hremP := hq.sub_of_mul_eq_left he hqe'
        rw [hremP.isIdempotentElem.eq]; abel
  have hconj : star b*q*b=a*q*star a := by
    calc
      _=star b*(p+w*q*star w)*b := by rw [←hfix]
      _=star b*e*b-(star b*b)*(star b*b)+(star b*b)*a*q*star a*(star b*b) := by
        dsimp [p,w,Link.final,b]; simp only [star_mul]; noncomm_ring
      _=a*q*star a := by
        have hsa : star a*f=star a := by
          simpa only [star_mul,hf.isSelfAdjoint.star_eq] using congrArg star hfa
        rw [mul_assoc (star b) e b,heb,hbi,hf.isIdempotentElem.eq,sub_self,zero_add,hfa]
        rw [mul_assoc (a*q) (star a) f,hsa]
  have hrf : r*star r=f := by
    have hqq : q*(e-q)=0 := by rw [mul_sub,hqe',hq.isIdempotentElem.eq,sub_self]
    have hqq' : (e-q)*q=0 := by rw [sub_mul,heq,hq.isIdempotentElem.eq,sub_self]
    calc
      _=a*(q*q)*star a+a*(q*(e-q))*b+star b*((e-q)*q)*star a+star b*((e-q)*(e-q))*b := by
        dsimp [r]; simp only [star_add,star_mul,star_sub,star_star,hq.isSelfAdjoint.star_eq,he.isSelfAdjoint.star_eq]
        noncomm_ring
      _=a*q*star a+star b*(e-q)*b := by
        rw [hq.isIdempotentElem.eq,hqq,hqq',mul_zero,zero_mul,mul_zero,zero_mul,add_zero,add_zero,
          (hq.sub_of_mul_eq_left he hqe').isIdempotentElem.eq]
      _=f := by
        rw [mul_sub,sub_mul,hconj,mul_assoc (star b) e b,heb,hbi]; abel
  have hre : r*e=r := by
    dsimp [r]
    have hrq : (e-q)*e=e-q := by rw [sub_mul,he.isIdempotentElem.eq,hqe']
    rw [add_mul,mul_assoc a q e,hqe',mul_assoc (star b) (e-q) e,hrq]
  exact ⟨⟨r,M.add_mem (M.mul_mem u.mem hqM) (M.mul_mem (M.star_mem' v.mem) (M.sub_mem heM hqM)),
    by rw [mul_assoc,hri,hre],hri.le,hrf.le⟩,hri,hrf⟩

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertModuleSchroederBernstein
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.HilbertModuleSB

open HilbertBiprod PartialIsometryOrder

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

lemma mem_intertwinerAlgebra (T : Space H G →L[ℂ] Space H G) :
    T∈intertwinerAlgebra φ ψ ↔ ∀ a,block (φ a) (ψ a)*T=T*block (φ a) (ψ a) := by
  change T∈StarSubalgebra.centralizer ℂ ((diagHom φ ψ).range : Set _) ↔ _
  rw [←SetLike.mem_coe,StarSubalgebra.coe_centralizer,StarMemClass.star_coe_eq,Set.union_self]
  constructor
  · intro h a; exact h _ ⟨a,rfl⟩
  · rintro h _ ⟨a,rfl⟩; exact h a

lemma left_mem : left (H:=H) (G:=G) ∈ intertwinerAlgebra φ ψ :=
  (mem_intertwinerAlgebra φ ψ _).mpr (fun scalar => left_commutes (φ scalar) (ψ scalar))

lemma offDiagonal_apply (V : H →ₗᵢ[ℂ] G) (x : Space H G) :
    offDiagonal V x=WithLp.toLp 2 (0,V x.ofLp.1) := by
  simp only [offDiagonal,ContinuousLinearMap.comp_apply,adjoint_inlL,inrL_apply]
  rfl

lemma offDiagonal_initial (V : H →ₗᵢ[ℂ] G) :
    star (offDiagonal V)*offDiagonal V=left := by
  change (offDiagonal V).adjoint.comp (offDiagonal V)=left
  simp only [offDiagonal,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hr : (inrL (H:=H) (G:=G)).adjoint.comp inrL=1 :=
    (inr (H:=H) (G:=G)).adjoint_comp_self
  have hv := V.adjoint_comp_self
  simp only [ContinuousLinearMap.comp_assoc] at *
  rw [←ContinuousLinearMap.comp_assoc (inrL (H:=H) (G:=G)).adjoint (inrL (H:=H) (G:=G)),hr]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp]
  rw [←ContinuousLinearMap.comp_assoc V.toContinuousLinearMap.adjoint V.toContinuousLinearMap (inlL (H:=H) (G:=G)).adjoint,hv]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp,inl_adjoint]

lemma offDiagonal_right (V : H →ₗᵢ[ℂ] G) : right*offDiagonal V=offDiagonal V := by
  ext x
  simp only [mul_apply_eq_comp,offDiagonal_apply,block_apply]
  rfl

lemma offDiagonal_left (V : H →ₗᵢ[ℂ] G) : offDiagonal V*left=offDiagonal V := by
  ext x
  simp only [mul_apply_eq_comp,offDiagonal_apply,block_apply]
  rfl

lemma offDiagonal_mem (V : H →ₗᵢ[ℂ] G)
    (hV : ∀ a x,V (φ a x)=ψ a (V x)) : offDiagonal V∈intertwinerAlgebra φ ψ := by
  apply (mem_intertwinerAlgebra φ ψ _).mpr
  intro a
  ext x
  simp only [mul_apply_eq_comp,offDiagonal_apply,block_apply,map_zero]
  rw [hV]

lemma subEquivalent_of_embedding (V : H →ₗᵢ[ℂ] G)
    (hV : ∀ a x,V (φ a x)=ψ a (V x)) :
    SubEquivalent (intertwinerAlgebra φ ψ) left right := by
  let v := offDiagonal V
  have hi : star v*v=left := offDiagonal_initial V
  have ht : v*star v*v=v := by rw [mul_assoc,hi]; exact offDiagonal_left V
  have hp : IsStarProjection (v*star v) := ⟨by change (v*star v)*(v*star v)=v*star v; rw [←mul_assoc,ht],by simp⟩
  have hle : v*star v ≤ right := (hp.le_iff_mul_eq_right right_projection).mpr (by
    rw [←mul_assoc,offDiagonal_right])
  exact ⟨⟨v,offDiagonal_mem φ ψ V hV,ht,hi.le,hle⟩,hi⟩

lemma offDiagonalReverse_apply (V : G →ₗᵢ[ℂ] H) (x : Space H G) :
    offDiagonalReverse V x=WithLp.toLp 2 (V x.ofLp.2,0) := by
  simp only [offDiagonalReverse,ContinuousLinearMap.comp_apply,adjoint_inrL,inlL_apply]
  rfl

lemma offDiagonalReverse_initial (V : G →ₗᵢ[ℂ] H) :
    star (offDiagonalReverse V)*offDiagonalReverse V=right := by
  change (offDiagonalReverse V).adjoint.comp (offDiagonalReverse V)=right
  simp only [offDiagonalReverse,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hr : (inlL (H:=H) (G:=G)).adjoint.comp inlL=1 :=
    (inl (H:=H) (G:=G)).adjoint_comp_self
  have hv := V.adjoint_comp_self
  simp only [ContinuousLinearMap.comp_assoc] at *
  rw [←ContinuousLinearMap.comp_assoc (inlL (H:=H) (G:=G)).adjoint (inlL (H:=H) (G:=G)),hr]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp]
  rw [←ContinuousLinearMap.comp_assoc V.toContinuousLinearMap.adjoint V.toContinuousLinearMap (inrL (H:=H) (G:=G)).adjoint,hv]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp,inr_adjoint]

lemma offDiagonalReverse_left (V : G →ₗᵢ[ℂ] H) : left*offDiagonalReverse V=offDiagonalReverse V := by
  ext x
  simp only [mul_apply_eq_comp,offDiagonalReverse_apply,block_apply]
  rfl

lemma offDiagonalReverse_right (V : G →ₗᵢ[ℂ] H) : offDiagonalReverse V*right=offDiagonalReverse V := by
  ext x
  simp only [mul_apply_eq_comp,offDiagonalReverse_apply,block_apply]
  rfl

lemma offDiagonalReverse_mem (V : G →ₗᵢ[ℂ] H)
    (hV : ∀ a x,V (ψ a x)=φ a (V x)) : offDiagonalReverse V∈intertwinerAlgebra φ ψ := by
  apply (mem_intertwinerAlgebra φ ψ _).mpr
  intro a
  ext x
  simp only [mul_apply_eq_comp,offDiagonalReverse_apply,block_apply,map_zero]
  rw [hV]

lemma subEquivalent_of_reverse_embedding (V : G →ₗᵢ[ℂ] H)
    (hV : ∀ a x,V (ψ a x)=φ a (V x)) :
    SubEquivalent (intertwinerAlgebra φ ψ) right left := by
  let v := offDiagonalReverse V
  have hi : star v*v=right := offDiagonalReverse_initial V
  have ht : v*star v*v=v := by rw [mul_assoc,hi]; exact offDiagonalReverse_right V
  have hp : IsStarProjection (v*star v) := ⟨by change (v*star v)*(v*star v)=v*star v; rw [←mul_assoc,ht],by simp⟩
  have hle : v*star v≤left := (hp.le_iff_mul_eq_right left_projection).mpr (by
    rw [←mul_assoc,offDiagonalReverse_left])
  exact ⟨⟨v,offDiagonalReverse_mem φ ψ V hV,ht,hi.le,hle⟩,hi⟩

lemma link_component_isometry (N : VonNeumannAlgebra (Space H G))
    (v : Link N left right) (hi : v.initial=left) :
    Isometry (BiprodLinkColumn.component N v.adjoint) := by
  apply (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mpr
  rw [BiprodLinkColumn.component_square,Link.adjoint_final,hi]
  have hl : (left (H:=H) (G:=G)).comp inlL=inlL := by ext x; rfl
  rw [hl]
  exact (inl (H:=H) (G:=G)).adjoint_comp_self

lemma link_component_coisometry (N : VonNeumannAlgebra (Space H G))
    (v : Link N left right) (hf : v.final=right) :
    (BiprodLinkColumn.component N v.adjoint).comp
      (BiprodLinkColumn.component N v.adjoint).adjoint=1 := by
  have hl : v.val.comp (left (H:=H) (G:=G))=v.val := v.mul_source left_projection
  have hf' : v.val.comp v.val.adjoint=right := hf
  have hr : (right (H:=H) (G:=G)).comp inrL=inrL := by ext x; rfl
  have hs : v.adjoint.val.adjoint=v.val := by
    change (star v.val).adjoint=v.val
    simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint]
  rw [BiprodLinkColumn.component_adjoint,BiprodLinkColumn.component,hs]
  change (inrL.adjoint.comp (v.val.comp inlL)).comp
    (inlL.adjoint.comp (v.val.adjoint.comp inrL)) = 1
  calc
    _=inrL.adjoint.comp ((v.val.comp left).comp (v.val.adjoint.comp inrL)) := by
      simp only [←inl_adjoint,ContinuousLinearMap.comp_assoc]
    _=inrL.adjoint.comp ((v.val.comp v.val.adjoint).comp inrL) := by
      rw [hl,ContinuousLinearMap.comp_assoc]
    _=1 := by rw [hf',hr]; exact (inr (H:=H) (G:=G)).adjoint_comp_self

theorem exists_unitary_of_embeddings_oai
    (V : H →ₗᵢ[ℂ] G) (W : G →ₗᵢ[ℂ] H)
    (hV : ∀ a x,V (φ a x)=ψ a (V x))
    (hW : ∀ a x,W (ψ a x)=φ a (W x)) :
    ∃ U : H ≃ₗᵢ[ℂ] G, ∀ a x,U (φ a x)=ψ a (U x) := by
  let N := intertwinerAlgebra φ ψ
  obtain ⟨v,hi,hf⟩ := subEquivalent_antisymm N (left_mem φ ψ) left_projection right_projection
    (subEquivalent_of_embedding φ ψ V hV) (subEquivalent_of_reverse_embedding φ ψ W hW)
  let T := BiprodLinkColumn.component N v.adjoint
  let F : H →ₗᵢ[ℂ] G := ⟨T.toLinearMap,
    (AddMonoidHomClass.isometry_iff_norm T).mp (link_component_isometry N v hi)⟩
  have hsur : Function.Surjective F := by
    intro y
    refine ⟨T.adjoint y,?_⟩
    exact congrArg (fun R : G →L[ℂ] G => R y) (link_component_coisometry N v hf)
  refine ⟨LinearIsometryEquiv.ofSurjective F hsur,?_⟩
  intro a x
  have hc : block (φ a) (ψ a)*star v.adjoint.val=star v.adjoint.val*block (φ a) (ψ a) := by
    simpa only [Link.adjoint,star_star] using (mem_intertwinerAlgebra φ ψ v.val).mp v.mem a
  exact congrArg (fun R : H →L[ℂ] G => R x)
    (BiprodLinkColumn.component_intertwines N φ ψ v.adjoint a hc)

end Kadison.HilbertModuleSB

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.HilbertModuleSB.exists_unitary_of_embeddings_oai.{u_1, u_2, u_3} := @OAI.Kadison.HilbertModuleSB.exists_unitary_of_embeddings_oai.{u_1, u_2, u_3}
