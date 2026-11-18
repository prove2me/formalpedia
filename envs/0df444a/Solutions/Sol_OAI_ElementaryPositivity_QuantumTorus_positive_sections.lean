-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.positive_sections
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:00.072376+00:00
-- url     : https://prove2.me/submissions/b5929405-3e84-48ee-85d0-a7c24bfc71c3

import Mathlib
import Definitions.Def_OAIQ368Chrom008
import Definitions.Def_OAIQ368Chrom013
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_literal_isotropic_adjoint
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_wall_joint_induction

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPrecision
open Filter
open scoped LaurentSeries

lemma lowerBound_iff_orderTop (b : ℤ) (f : Series) :
    LowerBound b f ↔ (b : WithTop ℤ)≤f.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  simp only [LowerBound,WithTop.coe_lt_coe]

lemma lowerBound_order (f : Series) : LowerBound f.order f :=
  fun _ h=>HahnSeries.coeff_eq_zero_of_lt_order h

lemma lowerBound_add {b : ℤ} {f g : Series} (hf : LowerBound b f) (hg : LowerBound b g) :
    LowerBound b (f+g) := by
  intro j hj
  simp only [HahnSeries.coeff_add,hf j hj,hg j hj,add_zero]

lemma lowerBound_mul {a b : ℤ} {f g : Series} (hf : LowerBound a f) (hg : LowerBound b g) :
    LowerBound (a+b) (f*g) := by
  rw [lowerBound_iff_orderTop] at *
  rw [WithTop.coe_add,HahnSeries.orderTop_mul]
  exact add_le_add hf hg

lemma agrees_iff_sub {b : ℤ} {f g : Series} : Agrees b f g ↔ LowerBound b (f-g) := by
  simp only [Agrees,LowerBound,HahnSeries.coeff_sub,sub_eq_zero]

lemma agrees_refl (b : ℤ) (f : Series) : Agrees b f f := fun _ _=>rfl
lemma agrees_add {b : ℤ} {f f' g g' : Series} (hf : Agrees b f f') (hg : Agrees b g g') :
    Agrees b (f+g) (f'+g') := by
  intro j hj
  simp only [HahnSeries.coeff_add,hf j hj,hg j hj]
lemma agrees_neg {b : ℤ} {f g : Series} (h : Agrees b f g) : Agrees b (-f) (-g) := by
  intro j hj
  simp only [HahnSeries.coeff_neg,h j hj]

lemma agrees_mul {N a b : ℤ} {f f' g g' : Series}
    (hf : Agrees (N-b) f f') (hg : Agrees (N-a) g g')
    (hf' : LowerBound a f') (hgb : LowerBound b g) :
    Agrees N (f*g) (f'*g') := by
  rw [agrees_iff_sub] at *
  have h₁ := lowerBound_mul hf hgb
  have h₂ := lowerBound_mul hf' hg
  have he : f*g-f'*g'=(f-f')*g+f'*(g-g') := by ring
  rw [he]
  apply lowerBound_add
  · simpa using h₁
  · convert h₂ using 1
    all_goals try with_reducible_and_instances rfl
    omega

variable {ι : Type*} (l : Filter ι)

lemma converges_const (F : Series) : Converges l (fun _=>F) F :=
  fun N=>Eventually.of_forall (fun _=>agrees_refl N F)

lemma Converges.lowerBound {f : ι → Series} {F : Series} (h : Converges l f F)
    (b : ℤ) (hb : LowerBound b F) : ∀ᶠ i in l,LowerBound b (f i) := by
  filter_upwards [h b] with i hi
  intro j hj
  rw [hi j hj,hb j hj]

lemma Converges.add {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i+g i) (F+G) := by
  intro N
  filter_upwards [hf N,hg N] with i hi hj
  exact agrees_add hi hj

lemma Converges.neg {f : ι → Series} {F : Series} (hf : Converges l f F) :
    Converges l (fun i=> -f i) (-F) := by
  intro N
  exact (hf N).mono (fun _ hi=>agrees_neg hi)

lemma Converges.mul {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i*g i) (F*G) := by
  intro N
  filter_upwards [hf (N-G.order),hg (N-F.order),
    hg.lowerBound l G.order (lowerBound_order G)] with i hi hj hb
  exact agrees_mul hi hj (lowerBound_order F) hb

lemma Converges.sum {α : Type*} (s : Finset α) {f : α → ι → Series} {F : α → Series}
    (h : ∀a∈s,Converges l (f a) (F a)) :
    Converges l (fun i=>∑a∈s,f a i) (∑a∈s,F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using converges_const l 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (h a (Finset.mem_insert_self _ _)).add l (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))

end ElementaryPositivity.LaurentPrecision

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_r40199e_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_r40199e_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma torusConverges_const (F : Torus v Ω) : TorusConverges v Ω l (fun _=>F) F :=
  fun m=>converges_const l (F m)

lemma TorusConverges.sum {α : Type*} (s : Finset α)
    {f : α → ι → Torus v Ω} {F : α → Torus v Ω}
    (h : ∀a∈s,TorusConverges v Ω l (f a) (F a)) :
    TorusConverges v Ω l (fun i=>∑a∈s,f a i) (∑a∈s,F a) := by
  intro m
  simp only [Finsupp.finsetSum_apply]
  exact LaurentPrecision.Converges.sum l s (fun a ha=>h a ha m)

lemma torus_mul_finite (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) (m : M) :
    (f*g) m=∑x∈S,∑y∈T,
      (Finsupp.single (x+y) (f x*g y*(↑(v^(Ω x y)) : LaurentSeries ℚ)) : Torus v Ω) m := by
  change Torus.multiply v Ω f g m=_
  unfold Torus.multiply
  rw [Finsupp.sum_of_support_subset f hf _ (by intros; simp)]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finsupp.sum_of_support_subset g hg _ (by intros; simp),Finsupp.finsetSum_apply]

lemma TorusConverges.mul_of_support {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G)
    (S T : Finset M) (hS : ∀i,(f i).support⊆S) (hT : ∀i,(g i).support⊆T)
    (hSF : F.support⊆S) (hTG : G.support⊆T) :
    TorusConverges v Ω l (fun i=>f i*g i) (F*G) := by
  intro m
  simp only [torus_mul_finite v Ω S T _ _ (hS _) (hT _) m,
    torus_mul_finite v Ω S T F G hSF hTG m]
  apply LaurentPrecision.Converges.sum l S
  intro x hx
  apply LaurentPrecision.Converges.sum l T
  intro y hy
  by_cases hxy : x+y=m
  · simp only [hxy,Finsupp.single_eq_same]
    exact ((hf x).mul l (hg y)).mul l (converges_const l _)
  · simp only [Finsupp.single_eq_of_ne (Ne.symm hxy)]
    exact converges_const l 0

lemma rootGrade_support (n : ℕ) (f : Torus v Ω) (hf : f∈rootGrade v Ω C n) :
    f.support⊆(rootDegree_finite C n).toFinset := by
  intro m hm
  apply (rootDegree_finite C n).mem_toFinset.mpr
  by_contra h
  exact (Finsupp.mem_support_iff.mp hm) (hf m h)

lemma TorusConverges.mul_graded {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G)
    (n k : ℕ) (hfn : ∀i,f i∈rootGrade v Ω C n) (hgk : ∀i,g i∈rootGrade v Ω C k)
    (hFn : F∈rootGrade v Ω C n) (hGk : G∈rootGrade v Ω C k) :
    TorusConverges v Ω l (fun i=>f i*g i) (F*G) :=
  hf.mul_of_support v Ω l hg (rootDegree_finite C n).toFinset (rootDegree_finite C k).toFinset
    (fun i=>rootGrade_support v Ω C n _ (hfn i))
    (fun i=>rootGrade_support v Ω C k _ (hgk i))
    (rootGrade_support v Ω C n F hFn) (rootGrade_support v Ω C k G hGk)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootTruncation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma cut_congr {N : ℕ} {F G : PowerSeries A} (h : ∀n≤N,coeff n F=coeff n G) :
    cut N F=cut N G := by
  ext n
  simp only [coeff_cut]
  split_ifs with hn
  · exact h n hn
  · rfl
@[simp] lemma cut_cut (N : ℕ) (F : PowerSeries A) : cut N (cut N F)=cut N F :=
  cut_congr (fun _ hn=>coeff_cut_of_le F hn)
end
end RootTruncation
namespace QuantumTorus
open PowerSeries RootTruncation
section Continuity
open PowerSeries RootTruncation Filter LaurentPrecision
variable {M I J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M) (l : Filter J)
lemma SeriesGraded.cut (N : ℕ) {F : PowerSeries (Torus v Ω)} (hF : SeriesGraded v Ω C F) :
    SeriesGraded v Ω C (cut N F) := by
  intro n
  rw [coeff_cut]
  split_ifs
  · exact hF n
  · intro m hm; rfl
end Continuity
end QuantumTorus
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SeriesApproximation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter
noncomputable section
variable {M ι : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)

lemma testAgreement_refl (T : Finset (PrecisionTest (M:=M))) (F : PowerSeries (Torus v Ω)) :
    TestAgreement v Ω T F F := fun _ _=>agrees_refl _ _

lemma inPrecisionClosure_self {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
    (hF : F∈A) : InPrecisionClosure v Ω A F :=
  fun T=>⟨F,hF,testAgreement_refl v Ω T F⟩

lemma InPrecisionClosure.mono {A B : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
    (hF : InPrecisionClosure v Ω A F) (hAB : A⊆B) : InPrecisionClosure v Ω B F := by
  intro T
  obtain ⟨G,hG,H⟩:=hF T
  exact ⟨G,hAB hG,H⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInverse
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddCommGroupTorusLaurentSeriesRat
local instance instAddGroupTorusLaurentSeriesRat_2_r40199e_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_2_r40199e_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma TorusConverges.neg {f : ι → Torus v Ω} {F : Torus v Ω}
    (hf : TorusConverges v Ω l f F) :
    TorusConverges v Ω l (fun i=> -f i) (-F) :=
  fun m=>(hf m).neg l

theorem SeriesConverges.inverse {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) :
    SeriesConverges v Ω l (fun i=>PowerSeries.invOfUnit (f i) 1) (PowerSeries.invOfUnit F 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    change TorusConverges v Ω l (fun i=>coeff n (PowerSeries.invOfUnit (f i) 1)) _
    have he := fun i=>coeff_inverse_one v Ω (f i) n
    simp_rw [funext he]
    rw [coeff_inverse_one]
    by_cases hn : n=0
    · simp only [ite_eq_left hn]
      exact torusConverges_const v Ω l 1
    · simp only [ite_eq_right hn]
      apply TorusConverges.neg
      apply TorusConverges.sum
      intro p hp
      by_cases hp2 : p.2<n
      · simp only [ite_eq_left hp2]
        exact (hf p.1).mul_graded v Ω C l (ih p.2 hp2) p.1 p.2
          (fun i=>hfg i p.1) (fun i=>(hfg i).inverse v Ω C p.2)
          (hF p.1) (hF.inverse v Ω C p.2)
      · simp only [ite_eq_right hp2]
        exact torusConverges_const v Ω l 0

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma inverse_mul (F G : PowerSeries A) (hF : constantCoeff F=1) (hG : constantCoeff G=1) :
    invOfUnit (F*G) 1=invOfUnit G 1*invOfUnit F 1 := by
  have hh : F*G*(invOfUnit G 1*invOfUnit F 1)=1:=by
    calc
      _=F*(G*invOfUnit G 1)*invOfUnit F 1:=by simp only [mul_assoc]
      _=1:=by rw [mul_invOfUnit G 1 hG,mul_one,mul_invOfUnit F 1 hF]
  calc
    _=invOfUnit (F*G) 1*(F*G*(invOfUnit G 1*invOfUnit F 1)):=by rw [hh,mul_one]
    _=(invOfUnit (F*G) 1*(F*G))*(invOfUnit G 1*invOfUnit F 1):=by simp only [mul_assoc]
    _=invOfUnit G 1*invOfUnit F 1:=by rw [invOfUnit_mul _ 1 (by simp [hF,hG]),one_mul]
lemma adjoint_mul (F G X : PowerSeries A) (hF : constantCoeff F=1) (hG : constantCoeff G=1) :
    adjoint (F*G) X=adjoint F (adjoint G X) := by
  simp only [adjoint,inverse_mul F G hF hG,mul_assoc]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open LaurentPrecision
noncomputable section

lemma positive_zero : Positive 0 := fun _=>natCoeff_zero
lemma Positive.add {f g : LaurentSeries ℚ} (hf : Positive f) (hg : Positive g) : Positive (f+g) :=
  fun j=>(hf j).add (hg j)
lemma Positive.sum {A : Type*} (s : Finset A) (f : A → LaurentSeries ℚ)
    (h : ∀a∈s,Positive (f a)) : Positive (∑a∈s,f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact positive_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))

lemma of_converges {A : Type*} (l : Filter A) [l.NeBot]
    {f : A → LaurentSeries ℚ} {F : LaurentSeries ℚ}
    (h : Converges l f F) (hp : ∀ᶠi in l,Positive (f i)) : Positive F := by
  intro j
  obtain ⟨i,hi,hpi⟩:=Filter.Eventually.exists ((h (j+1)).and hp)
  rw [←hi j (by omega)]
  exact hpi j

end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootClosureFacts
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter
open WallUnits
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M)
variable {A : Set (PowerSeries (Torus LaurentRay.vUnit Ω))}
variable {F : PowerSeries (Torus LaurentRay.vUnit Ω)}

lemma InPrecisionClosure.graded
    (hF : InPrecisionClosure LaurentRay.vUnit Ω A F)
    (hA : ∀G∈A,SeriesGraded LaurentRay.vUnit Ω C G) :
    SeriesGraded LaurentRay.vUnit Ω C F := by
  classical
  intro n m hm
  ext j
  obtain ⟨G,hG,H⟩:=hF {(n,m,j+1)}
  have HH:=H (n,m,j+1) (by simp) j (by dsimp; omega)
  dsimp only at HH
  rw [hA G hG n m hm] at HH
  exact HH.symm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_TruncatedPrecisionClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation LaurentPrecision Filter WallUnits
noncomputable section
variable {M I J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)
lemma RootClosedThrough.congr {N : ℕ} {A : Set (PowerSeries (Torus v Ω))}
    {F G : PowerSeries (Torus v Ω)} (hF : RootClosedThrough v Ω N A F)
    (he : ∀n≤N,coeff n F=coeff n G) : RootClosedThrough v Ω N A G := by
  change InPrecisionClosure v Ω _ _ at hF ⊢
  rw [←cut_congr he]
  exact hF
lemma InPrecisionClosure.cut {A : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : InPrecisionClosure v Ω A F) (N : ℕ) :
    RootClosedThrough v Ω N A F := by
  intro T
  obtain ⟨G,hG,H⟩:=hF T
  refine ⟨RootTruncation.cut N G,⟨G,hG,rfl⟩,?_⟩
  intro t ht
  simp only [coeff_cut]
  by_cases hn : t.1≤N
  · simp only [hn,ite_true, if_true]; exact H t ht
  · simp only [hn,ite_false, if_false]; exact agrees_refl _ _
lemma rootClosedThrough_self {N : ℕ} {A : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : F∈A) : RootClosedThrough v Ω N A F :=
  inPrecisionClosure_self v Ω ⟨F,hF,rfl⟩
lemma RootClosedThrough.mono {N : ℕ} {A B : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : RootClosedThrough v Ω N A F) (hAB : A⊆B) :
    RootClosedThrough v Ω N B F := InPrecisionClosure.mono v Ω hF (Set.image_mono hAB)
variable {N : ℕ} {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
lemma rootApprox_mem (hF : RootClosedThrough v Ω N A F)
    (T : Finset (PrecisionTest (M:=M))) : rootApprox v Ω hF T∈A :=
  (Classical.choose_spec (rootClosedThrough_approx_exists v Ω hF T)).1
lemma rootApprox_converges (hF : RootClosedThrough v Ω N A F) :
    SeriesConverges v Ω (atTop : Filter (Finset (PrecisionTest (M:=M))))
      (fun T=>RootTruncation.cut N (rootApprox v Ω hF T)) (RootTruncation.cut N F) := by
  classical
  intro n m K
  apply eventually_atTop.mpr
  refine ⟨{(n,m,K)},fun T hT=>?_⟩
  exact (Classical.choose_spec (rootClosedThrough_approx_exists v Ω hF T)).2
    (n,m,K) (hT (by simp))
end

end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SectionTrace
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
local instance sectionTraceAddCommGroup_r40199e_1 : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance sectionTraceAddGroup_r40199e_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance sectionTraceSub_r40199e_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma torus_eval_sum {J : Type*} (s : Finset J) (f : J → Torus v Ω) (r : M) :
    (∑j∈s,f j) r=∑j∈s,f j r := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    change f j r+(∑j∈s,f j) r=_
    rw [ih]
include hΩ in
lemma series_coefficient_trace (r : M) (F X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,∀m,Ω m r≠0 → (coeff n F) m=0) :
    (coeff N (F*X)) r=(coeff N (X*F)) r := by
  classical
  rw [coeff_mul,coeff_mul]
  change (∑p∈Finset.HasAntidiagonal.antidiagonal N, ((coeff p.1 F)*(coeff p.2 X) : Torus v Ω)) r =
    (∑p∈Finset.HasAntidiagonal.antidiagonal N, ((coeff p.1 X)*(coeff p.2 F) : Torus v Ω)) r
  rw [torus_eval_sum,torus_eval_sum]
  rw [←Finset.Nat.sum_antidiagonal_swap (f:=fun p=>((coeff p.1 X)*(coeff p.2 F)) r)]
  apply Finset.sum_congr rfl
  intro p hp
  apply coefficient_trace v Ω hΩ r
  exact hF p.1 (by have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega)
include hΩ in
lemma adjoint_coefficient_trace (r : M) (F X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF0 : constantCoeff F=1)
    (hF : ∀n≤N,∀m,Ω m r≠0 → (coeff n F) m=0) :
    (coeff N (adjoint F X)) r=(coeff N X) r := by
  unfold adjoint
  rw [mul_assoc,series_coefficient_trace v Ω hΩ r F (X*invOfUnit F 1) N hF,
    mul_assoc,invOfUnit_mul F 1 hF0,mul_one]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ChartRefinement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
theorem chart_negative_refinement (h k H : M→+ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hsign : ∀n≤N,∀m,HasRootDegree C n m→LexSigns h k H m) :
    ∀n≤N,coeff n (chartNegative v Ω C H F).val=
      coeff n ((chartNegative v Ω C k (chartZero v Ω C h F)).val *
        (chartNegative v Ω C h F).val) :=by
  let A:=chartPositive v Ω C h F
  let B:=chartZero v Ω C h F
  let D:=chartNegative v Ω C h F
  let A0:=chartPositive v Ω C k B
  let B0:=chartZero v Ω C k B
  let D0:=chartNegative v Ω C k B
  have hfact : (A.val*A0.val)*B0.val*(D0.val*D.val)=F.val :=by
    calc
      _=A.val*(A0.val*B0.val*D0.val)*D.val:=by simp only [mul_assoc]
      _=A.val*B.val*D.val:=by rw [chart_three_factorization v Ω C k B]
      _=F.val:=chart_three_factorization v Ω C h F
  have hs:=chart_three_support v Ω C h F
  have hs0:=chart_three_support v Ω C k B
  have hker:=chartThree_supported v Ω C k h.ker.toAddSubmonoid B
    (chartZero_supported_kernel v Ω C h F)
  have hA : ∀n,n+1≤N→SupportedOn v Ω (fun m=>0<H m) (coeff (n+1) A.val):=by
    intro n hn m hm
    by_contra hx
    exact hm ((hsign _ hn m (chart_root_of_ne v Ω C A _ m hx)).1 (hs.1 n m hx))
  have hA0 : ∀n,n+1≤N→SupportedOn v Ω (fun m=>0<H m) (coeff (n+1) A0.val):=by
    intro n hn m hm
    by_contra hx
    have hz : h m=0:=by by_contra hh; exact hx (hker.1 (n+1) m hh)
    exact hm (((hsign _ hn m (chart_root_of_ne v Ω C A0 _ m hx)).2.2 hz).1 (hs0.1 n m hx))
  have hD : ∀n,n+1≤N→SupportedOn v Ω (fun m=>H m<0) (coeff (n+1) D.val):=by
    intro n hn m hm
    by_contra hx
    exact hm ((hsign _ hn m (chart_root_of_ne v Ω C D _ m hx)).2.1 (hs.2.2 n m hx))
  have hD0 : ∀n,n+1≤N→SupportedOn v Ω (fun m=>H m<0) (coeff (n+1) D0.val):=by
    intro n hn m hm
    by_contra hx
    have hz : h m=0:=by by_contra hh; exact hx (hker.2.2 (n+1) m hh)
    exact hm (((hsign _ hn m (chart_root_of_ne v Ω C D0 _ m hx)).2.2 hz).2.2 (hs0.2.2 n m hx))
  have hB0 : ∀n,n+1≤N→∀m,coeff (n+1) B0.val m≠0→H m=0:=by
    intro n hn m hm
    have hz : h m=0:=by by_contra hh; exact hm (hker.2.1 (n+1) m hh)
    exact ((hsign _ hn m (chart_root_of_ne v Ω C B0 _ m hm)).2.2 hz).2.1 (hs0.2.1 n m hm)
  have hAA:=strict_mul_through v Ω (fun m=>0<H m)
    (fun a b ha hb=>by rw [map_add]; linarith) A.val A0.val N A.property.1 A0.property.1 hA hA0
  have hDD:=strict_mul_through v Ω (fun m=>H m<0)
    (fun a b ha hb=>by rw [map_add]; linarith) D0.val D.val N D0.property.1 D.property.1 hD0 hD
  have hu:=chart_three_truncated_unique v Ω C H F (A.val*A0.val) B0.val (D0.val*D.val) N
    (by simp [A.property.1,A0.property.1]) B0.property.1
    (by simp [D0.property.1,D.property.1]) hfact
    (fun n hn m hm=>by by_contra hh; exact hm (hAA n hn m hh)) hB0
    (fun n hn m hm=>by by_contra hh; exact hm (hDD n hn m hh))
  exact fun n hn=>(hu n hn).2.2.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TranslatedCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.shiftRootGradeAddCommGroup
local instance shiftRootGradeSub_r40199e_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.shiftRootGradeAddGroup
lemma shiftRootGrade_mul (b c : M) (n k : ℕ) (f g : Torus v Ω)
    (hf : f∈shiftRootGrade v Ω C b n) (hg : g∈shiftRootGrade v Ω C c k) :
    f*g∈shiftRootGrade v Ω C (b+c) (n+k) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hxC : HasRootDegree C n (x-b):=by by_contra hn; exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
  have hyC : HasRootDegree C k (y-c):=by by_contra hn; exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
  apply Finsupp.single_eq_of_ne
  intro he
  apply hm
  rw [he]
  convert rootDegree_add C hxC hyC using 1 <;> first | (with_reducible_and_instances rfl) | (abel)
lemma ShiftGraded.mul {b c : M} {X Y : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (hY : ShiftGraded v Ω C c Y) :
    ShiftGraded v Ω C (b+c) (X*Y) := by
  intro n
  rw [coeff_mul]
  apply (shiftRootGrade v Ω C (b+c) n).sum_mem
  intro p hp
  rw [←Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  exact shiftRootGrade_mul v Ω C b c p.1 p.2 _ _ (hX p.1) (hY p.2)
lemma shiftGraded_zero_iff (F : PowerSeries (Torus v Ω)) :
    ShiftGraded v Ω C 0 F↔SeriesGraded v Ω C F := by
  simp only [ShiftGraded,SeriesGraded,shiftRootGrade,rootGrade,AddSubgroup.mem_mk,sub_zero]
lemma ShiftGraded.adjoint {b : M} {X : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (F : CompletedPositive v Ω C) :
    ShiftGraded v Ω C b (adjoint F.val X) := by
  have hF:=(shiftGraded_zero_iff v Ω C F.val).mpr F.property.2
  have hI:=(shiftGraded_zero_iff v Ω C (completedInverse v Ω C F).val).mpr
    (completedInverse v Ω C F).property.2
  simpa only [zero_add,add_zero,PowerSeriesAdjoint.adjoint,completedInverse] using (hF.mul v Ω C hX).mul v Ω C hI
lemma ShiftGraded.sectionValue {b : M} {X : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (F : CompletedPositive v Ω C) (h : M →+ ℝ) :
    ShiftGraded v Ω C b (sectionValue v Ω C F h X) :=
  hX.adjoint v Ω C (chartNegative v Ω C h F)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (q : M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.chargeGradeAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.chargeGradeAddGroup
local instance chargeGradeSub_r40199e_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma chargeGrade_one : (1:Torus v Ω)∈chargeGrade v Ω q 0 := by
  intro m hm
  change (Finsupp.single 0 (1:LaurentSeries ℚ)) m=0
  apply Finsupp.single_eq_of_ne
  intro he
  exact hm (by rw [he,map_zero])
lemma chargeGrade_X (m : M) : Torus.X v Ω m∈chargeGrade v Ω q (q m) := by
  intro r hr
  change (Finsupp.single m (1:LaurentSeries ℚ)) r=0
  apply Finsupp.single_eq_of_ne
  exact fun he=>hr (congrArg q he)
lemma chargeGrade_mul (a b : ℤ) (f g : Torus v Ω)
    (hf : f∈chargeGrade v Ω q a) (hg : g∈chargeGrade v Ω q b) :
    f*g∈chargeGrade v Ω q (a+b) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hxq : q x=a:=by by_contra hn; exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
  have hyq : q y=b:=by by_contra hn; exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
  apply Finsupp.single_eq_of_ne
  intro he
  apply hm
  rw [he,map_add,hxq,hyq]
lemma chargeGrade_series_mul (a b : ℤ) (F G : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,coeff n F∈chargeGrade v Ω q a)
    (hG : ∀n≤N,coeff n G∈chargeGrade v Ω q b) :
    coeff N (F*G)∈chargeGrade v Ω q (a+b) := by
  rw [coeff_mul]
  apply (chargeGrade v Ω q (a+b)).sum_mem
  intro p hp
  have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact chargeGrade_mul v Ω q a b _ _ (hF p.1 (by omega)) (hG p.2 (by omega))
lemma chargeGrade_inverse (F : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,coeff n F∈chargeGrade v Ω q 0) :
    ∀n≤N,coeff n (invOfUnit F 1)∈chargeGrade v Ω q 0 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_inverse_one]
    split_ifs with h0
    · exact chargeGrade_one v Ω q
    · apply (chargeGrade v Ω q 0).neg_mem
      apply (chargeGrade v Ω q 0).sum_mem
      intro p hp
      split_ifs with hp2
      · have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        simpa only [add_zero] using chargeGrade_mul v Ω q 0 0 _ _
          (hF p.1 (by omega)) (ih p.2 hp2 (by omega))
      · exact (chargeGrade v Ω q 0).zero_mem
lemma adjoint_charge (F : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,coeff n F∈chargeGrade v Ω q 0) (m : M) :
    coeff N (adjoint F (PowerSeries.C (Torus.X v Ω m)))∈chargeGrade v Ω q (q m) := by
  have hm : ∀n≤N,coeff n (PowerSeries.C (Torus.X v Ω m))∈chargeGrade v Ω q (q m):=by
    intro n hn
    rw [coeff_C]
    split_ifs
    · exact chargeGrade_X v Ω q m
    · exact (chargeGrade v Ω q (q m)).zero_mem
  have hFI : ∀n≤N,coeff n (F*PowerSeries.C (Torus.X v Ω m))∈chargeGrade v Ω q (q m):=by
    intro n hn
    simpa only [zero_add] using chargeGrade_series_mul v Ω q 0 (q m) _ _ n
      (fun j hj=>hF j (hj.trans hn)) (fun j hj=>hm j (hj.trans hn))
  simpa only [add_zero,adjoint] using chargeGrade_series_mul v Ω q (q m) 0 _ _ N hFI
    (chargeGrade_inverse v Ω q F N hF)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SectionCharts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma negative_sign_congr_through (h k : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m →
      (0<h m → 0<k m) ∧ (h m=0 → k m=0) ∧ (h m<0 → k m<0)) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n (chartNegative v Ω C k F).val := by
  have H:=chart_three_support v Ω C h F
  have HU:=chart_three_truncated_unique v Ω C k F
    (chartPositive v Ω C h F).val (chartZero v Ω C h F).val (chartNegative v Ω C h F).val N
    (chartPositive v Ω C h F).property.1 (chartZero v Ω C h F).property.1
    (chartNegative v Ω C h F).property.1 (chart_three_factorization v Ω C h F)
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).1 (H.1 n m hm))
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).2.1 (H.2.1 n m hm))
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).2.2 (H.2.2 n m hm))
  exact fun n hn=>(HU n hn).2.2
lemma section_sign_congr_through (h k : M →+ ℝ) (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m →
      (0<h m → 0<k m) ∧ (h m=0 → k m=0) ∧ (h m<0 → k m<0)) :
    ∀n≤N,coeff n (sectionValue v Ω C F h X)=coeff n (sectionValue v Ω C F k X) := by
  intro n hn
  exact adjoint_coeff_congr _ _ _ _ n
    (fun j hj=>negative_sign_congr_through v Ω C h k F N hs j (hj.trans hn)) (fun _ _=>rfl)
lemma section_refinement_through (h k H : M →+ ℝ) (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (sectionValue v Ω C F H X)=
      coeff n (adjoint (chartNegative v Ω C k (chartZero v Ω C h F)).val
        (sectionValue v Ω C F h X)) := by
  intro n hn
  unfold sectionValue
  rw [←adjoint_mul _ _ _ (chartNegative v Ω C k (chartZero v Ω C h F)).property.1
    (chartNegative v Ω C h F).property.1]
  exact adjoint_coeff_congr _ _ _ _ n
    (fun j hj=>chart_negative_refinement v Ω C h k H F N hs j (hj.trans hn)) (fun _ _=>rfl)
lemma section_incoming_perturbation (hΩ : ∀m,Ω m m=0) (r : M) (k H : M →+ ℝ)
    (F : CompletedPositive v Ω C) (X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns (incomingCovector Ω r) k H m) :
    (coeff N (sectionValue v Ω C F H X)) r=
      (coeff N (sectionValue v Ω C F (incomingCovector Ω r) X)) r := by
  rw [section_refinement_through v Ω C _ _ _ F X N hs N le_rfl]
  apply adjoint_coefficient_trace v Ω hΩ r _ _ N
    (chartNegative v Ω C k (chartZero v Ω C (incomingCovector Ω r) F)).property.1
  have hker:=chartThree_supported v Ω C k (incomingCovector Ω r).ker.toAddSubmonoid
    (chartZero v Ω C (incomingCovector Ω r) F) (chartZero_supported_kernel v Ω C _ F)
  intro n hn m hm
  apply hker.2.2 n m
  intro hh
  apply hm
  change (Ω m r:ℝ)=0 at hh
  exact_mod_cast hh
lemma chartNegative_of_positive_through (h : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hpos : ∀n,n+1≤N → ∀m,coeff (n+1) F.val m≠0 → 0<h m) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n 1 := by
  have H:=chart_three_truncated_unique v Ω C h F F.val 1 1 N F.property.1 (by simp)
    (by simp) (by simp) hpos (by intro n hn m hm; simp at hm) (by intro n hn m hm; simp at hm)
  exact fun n hn=>(H n hn).2.2.symm
lemma chartNegative_of_negative_through (h : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hneg : ∀n,n+1≤N → ∀m,coeff (n+1) F.val m≠0 → h m<0) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n F.val := by
  have H:=chart_three_truncated_unique v Ω C h F 1 1 F.val N (by simp) (by simp)
    F.property.1 (by simp) (by intro n hn m hm; simp at hm) (by intro n hn m hm; simp at hm) hneg
  exact fun n hn=>(H n hn).2.2.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_AdjointExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries RootTruncation
noncomputable section
variable {A : Type*} [Ring A]
lemma coeff_adjoint_lower (F X : PowerSeries A) (hF : constantCoeff F=1) (N : ℕ) :
    coeff N (adjoint F X)=coeff N X+
      ∑j∈Finset.range N,coeff (N-j) (adjoint F (PowerSeries.C (coeff j X))) := by
  rw [coeff_adjoint_expansion,Finset.sum_range_succ,Nat.sub_self,coeff_zero_eq_constantCoeff,
    constant_adjoint F _ hF,constantCoeff_C,add_comm]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteElementaryAdjoint
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma adjoint_one (X : PowerSeries A) : adjoint 1 X=X := by
  have hI : invOfUnit (1:PowerSeries A) 1=1:=by
    have H:=mul_invOfUnit (1:PowerSeries A) 1 (by simp)
    simpa using H
  simp only [adjoint,one_mul,hI,mul_one]
lemma adjoint_inverse_cancel (F X : PowerSeries A) (hF : constantCoeff F=1) :
    adjoint (invOfUnit F 1) (adjoint F X)=X := by
  rw [←adjoint_mul _ _ _ (by simp) hF,invOfUnit_mul F 1 hF,adjoint_one]
lemma adjoint_inverse_coeff (F X Y : PowerSeries A) (hF : constantCoeff F=1) (N : ℕ)
    (hXY : ∀n≤N,coeff n X=coeff n (adjoint F Y)) :
    coeff N (adjoint (invOfUnit F 1) X)=coeff N Y := by
  rw [adjoint_coeff_congr _ _ _ _ N (fun _ _=>rfl) hXY,adjoint_inverse_cancel F Y hF]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I→ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_3_r40199e_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_r40199e_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma torus_mul_support (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) : (f*g).support⊆sumSupport S T := by
  intro m hm
  by_contra H
  apply Finsupp.mem_support_iff.mp hm
  rw [torus_mul_finite v Ω S T f g hf hg m]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply Finsupp.single_eq_of_ne
  intro Hxy
  apply H
  exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,Hxy.symm⟩

lemma SeriesConverges.mul_of_support {f g : ι → PowerSeries (Torus v Ω)}
    {F G : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hg : SeriesConverges v Ω l g G)
    (S T : ℕ → Finset M) (hs : ∀i n,(coeff n (f i)).support⊆S n)
    (ht : ∀i n,(coeff n (g i)).support⊆T n)
    (hS : ∀n,(coeff n F).support⊆S n) (hT : ∀n,(coeff n G).support⊆T n) :
    SeriesConverges v Ω l (fun i=>f i*g i) (F*G) := by
  intro n
  simp only [coeff_mul]
  apply TorusConverges.sum
  intro p hp
  exact (hf p.1).mul_of_support v Ω l (hg p.2) (S p.1) (T p.2)
    (fun i=>hs i p.1) (fun i=>ht i p.2) (hS p.1) (hT p.2)

lemma SeriesConverges.mul_C {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hfg : ∀i,SeriesGraded v Ω C (f i))
    (hF : SeriesGraded v Ω C F) (x : Torus v Ω) :
    SeriesConverges v Ω l (fun i=>f i*PowerSeries.C x) (F*PowerSeries.C x) := by
  intro n
  simp only [coeff_mul_C]
  exact (hf n).mul_of_support v Ω l (torusConverges_const v Ω l x)
    (rootDegree_finite C n).toFinset x.support
    (fun i=>rootGrade_support v Ω C n _ (hfg i n)) (fun _=>Finset.Subset.refl _)
    (rootGrade_support v Ω C n _ (hF n)) (Finset.Subset.refl _)

lemma SeriesGraded.mul_C_support {F : PowerSeries (Torus v Ω)}
    (hF : SeriesGraded v Ω C F) (x : Torus v Ω) (n : ℕ) :
    (coeff n (F*PowerSeries.C x)).support⊆sumSupport (rootDegree_finite C n).toFinset x.support := by
  rw [coeff_mul_C]
  exact torus_mul_support v Ω _ _ _ _ (rootGrade_support v Ω C n _ (hF n)) (Finset.Subset.refl _)

theorem SeriesConverges.adjoint {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) (x : Torus v Ω) :
    SeriesConverges v Ω l (fun i=>f i*PowerSeries.C x*invOfUnit (f i) 1)
      (F*PowerSeries.C x*invOfUnit F 1) := by
  exact (hf.mul_C v Ω C l hfg hF x).mul_of_support v Ω l
    (hf.inverse v Ω C l hfg hF)
    (fun n=>sumSupport (rootDegree_finite C n).toFinset x.support)
    (fun n=>(rootDegree_finite C n).toFinset)
    (fun i n=>(hfg i).mul_C_support v Ω C x n)
    (fun i n=>rootGrade_support v Ω C n _ ((hfg i).inverse v Ω C n))
    (fun n=>hF.mul_C_support v Ω C x n)
    (fun n=>rootGrade_support v Ω C n _ (hF.inverse v Ω C n))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RayIncomingIdentification
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma OnPositiveRay.refl (r : M) : OnPositiveRay r r := ⟨1,1,one_pos,one_pos,by simp⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IsolatedPositivePlane
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M→+M→+ℤ)
lemma OnPositiveRay.pair_nonneg {r s p q : M} (hp : OnPositiveRay r p) (hq : OnPositiveRay s q)
    (h : 0≤Ω r s) : 0≤Ω p q := by
  have hright:=hq.incomingSigns Ω r
  have hleft:=hp.eval (incomingCovector Ω q)
  by_contra hn
  have hn' : incomingCovector Ω q p < 0:=by change (Ω p q:ℝ)<0; exact_mod_cast (lt_of_not_ge hn)
  have H:=hright.2.2.mpr (hleft.2.2.mp hn')
  change (Ω r s:ℝ)<0 at H
  have h' : (0:ℝ)≤Ω r s:=by exact_mod_cast h
  linarith
lemma OnPositiveRay.pair_zero {r p q : M} (hp : OnPositiveRay r p) (hq : OnPositiveRay r q)
    (hΩ : Ω r r=0) : Ω p q=0 := by
  have hright:=hq.incomingSigns Ω r
  have hleft:=hp.eval (incomingCovector Ω q)
  have H : incomingCovector Ω r r=0:=by change (Ω r r:ℝ)=0; rw [hΩ,Int.cast_zero]
  have HH:=hleft.2.1.mpr (hright.2.1.mp H)
  change (Ω p q:ℝ)=0 at HH
  exact_mod_cast HH
lemma literalRootProducts_allowed_mono (C : (I→ℤ)→+M) (P Q : M→Prop)
    (H : ∀n,0<n → ∀p,HasRootDegree C n p → P p → Q p) :
    literalRootProducts Ω C P⊆literalRootProducts Ω C Q := by
  rintro F ⟨l,hl,rfl⟩
  refine ⟨l,?_,rfl⟩
  intro u hu
  have h:=hl u hu
  exact ⟨h.1,h.2.1,H u.degree h.1 u.root h.2.1 h.2.2⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteSignCharts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
omit [Algebra ℚ R] in
lemma RayGeneric.ray_supported {N : ℕ} {r : M} {h : M →+ ℝ}
    (H : RayGeneric C N r h) (F : CompletedPositive v Ω C) :
    ∀n,0 < n → n ≤ N → SupportedOn v Ω (OnPositiveRay r)
      (coeff n (chartZero v Ω C h F).val) := by
  intro n hn hN m hm
  by_contra hx
  have hr:=chart_root_of_ne v Ω C _ _ m hx
  cases n with
  | zero => omega
  | succ n => exact hm (H.2 (n+1) hn hN m hr ((chart_three_support v Ω C h F).2.1 n m hx))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusAdjointExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint LaurentPositive WallUnits
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorusLaurentSeriesRatVUnit_1
local instance instAddCommGroupTorusLaurentSeriesRatVUnit_r40199e_1 : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatVUnit_1_r40199e_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instSubTorusLaurentSeriesRatVUnit_r40199e_1 : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
lemma adjoint_target_positive (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (f : Torus LaurentRay.vUnit Ω) (q : M →+ ℤ) (N : ℕ) (r : M)
    (hF : ∀n≤N,coeff n F∈chargeGrade LaurentRay.vUnit Ω q 0)
    (hf : TorusPositive Ω f)
    (hp : ∀m,q m=q r → Positive (coeff N (adjoint F (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) r)) :
    Positive (coeff N (adjoint F (PowerSeries.C f)) r) := by
  classical
  rw [adjoint_torus_expansion]
  apply Positive.sum
  intro m hm
  by_cases hq : q m=q r
  · exact (hf m).mul (hp m hq)
  · have H:=adjoint_charge LaurentRay.vUnit Ω q F N hF m r (Ne.symm hq)
    rw [H,mul_zero]
    exact positive_zero
lemma adjoint_increment_positive (F X : PowerSeries (Torus LaurentRay.vUnit Ω))
    (q : M →+ ℤ) (N : ℕ) (r : M) (hF0 : constantCoeff F=1)
    (hF : ∀n≤N,coeff n F∈chargeGrade LaurentRay.vUnit Ω q 0)
    (hX : ∀j<N,TorusPositive Ω (coeff j X))
    (hp : ∀m,q m=q r → ∀j≤N,Positive (coeff j (adjoint F (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) r)) :
    Positive (coeff N (adjoint F X) r-coeff N X r) := by
  rw [coeff_adjoint_lower F X hF0 N]
  change Positive ((coeff N X) r+(∑j∈Finset.range N,coeff (N-j) (adjoint F (PowerSeries.C (coeff j X)))) r-(coeff N X) r)
  rw [add_sub_cancel_left,torus_ring_eval_sum]
  apply Positive.sum
  intro j hj
  exact adjoint_target_positive Ω F (coeff j X) q (N-j) r
    (fun n hn=>hF n (hn.trans (Nat.sub_le _ _))) (hX j (Finset.mem_range.mp hj))
    (fun m hm=>hp m hm _ (Nat.sub_le _ _))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallLineInitial
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
theorem incoming_positive_at_far (N d : ℕ) (r : M) (hd : 0 < d) (hr : HasRootDegree C d r)
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (F D : CompletedPositive LaurentRay.vUnit Ω C)
    (hD : ∀n m,coeff (n+1) D.val m≠0 → OnPositiveRay r m)
    (hpos : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r)) D.val)
    (hprescribed : ∀n ≤ N,∀m,OnPositiveRay r m →
      coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m) F).val) m=
        coeff n (FormalLog.log D.val) m) :
    ∃b,0 < b ∧ (∀a∈lineEvents (realRootsThrough e C N) (B.flip (e r)) k,a < b) ∧
      RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+b • B.flip (e r)).toAddMonoidHom.comp e) F).val := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  obtain ⟨b,hb,hbound⟩:=finite_upper_bound (lineEvents (realRootsThrough e C N) (B.flip (e r)) k)
  refine ⟨b,hb,hbound,?_⟩
  have Hgen:=offset_ray_generic C e he L hdeg N d r hd hr (B.flip (e r)) k H
  have Hinc:=incoming_ray_element_through LaurentRay.vUnit Ω C hΩ r (k.toAddMonoidHom.comp e)
    H.on_ray F D N (fun n hn hnN m hm hΩm hkm => Hgen.2 n hn hnN m hm hkm) hD hprescribed
  have Href:=chart_zero_refinement LaurentRay.vUnit Ω C (incomingCovector Ω r)
    (k.toAddMonoidHom.comp e) ((k+b • B.flip (e r)).toAddMonoidHom.comp e) F N (by
      intro n hn m hm
      have HH:=far_line_lex (realRootsThrough e C N) (B.flip (e r)) k b hbound
        (e m) (realRoot_mem e C N n hn m hm)
      simp only [LinearMap.flip_apply,hcomp] at HH
      exact HH)
  apply hpos.congr LaurentRay.vUnit Ω
  intro n hn
  exact (Href n hn |>.trans (Hinc n hn)).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GlobalWallPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry FiniteEventTraversal WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

lemma literalRootProducts_one (P : M → Prop) :
    (1 : PowerSeries (Torus LaurentRay.vUnit Ω))∈literalRootProducts Ω C P :=
  ⟨[],by simp,by simp⟩
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

theorem positive_walls_through (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) : ∀N,WallsPositiveThrough Ω C e N F := by
  intro N
  induction N with
  | zero =>
    intro r d hd hr h hg
    have H:=rootClosedThrough_self LaurentRay.vUnit Ω (N:=0) (literalRootProducts_one Ω C (OnPositiveRay r))
    apply H.congr LaurentRay.vUnit Ω
    intro i hi
    have hi0 : i=0:=by omega
    subst i
    rw [coeff_zero_eq_constantCoeff,map_one,(chartZero LaurentRay.vUnit Ω C _ F).property.1]
  | succ n ih =>
    intro r d hd hr h hg
    let S:=realRootsThrough e C (n+1)
    let vR:=B.flip (e r)
    obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset S (e r) vR h hg.1
    let events:=lineEvents S vR k
    let P (a : ℝ):=RootClosedThrough LaurentRay.vUnit Ω (n+1)
      (literalRootProducts Ω C (OnPositiveRay r))
      (chartZero LaurentRay.vUnit Ω C ((k+a • vR).toAddMonoidHom.comp e) F).val
    have h0 : (0:ℝ)∉events:=by
      intro hevent
      obtain ⟨s,hs,hv,hs0⟩:=(mem_lineEvents_iff S vR k 0).mp hevent
      have hn : s∉Submodule.span ℝ {e r}:=by
        intro hmem
        obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp hmem
        apply hv
        rw [←hc,map_smul]
        change c*B (e r) (e r)=0
        rw [hB,mul_zero]
      apply Hk.avoid s hs hn
      simpa only [zero_smul,add_zero] using hs0
    have hstart : ∃b,0 ≤ b ∧ (∀a∈events,a < b) ∧ P b:=by
      obtain ⟨D,hD,hpos,hpres⟩:=incoming r d hd hr
      obtain ⟨b,hb,hbound,hwall⟩:=incoming_positive_at_far Ω C e he B hB hcomp L hdeg
        (n+1) d r hd hr k Hk F D hD (hpos.cut LaurentRay.vUnit Ω (n+1))
        (fun j hj m hm => hpres j m hm)
      exact ⟨b,hb.le,hbound,hwall⟩
    have hcell : ∀a b,0 ≤ a → 0 ≤ b → a∉events → b∉events →
        (∀z∈events,a < z ↔ b < z) → P a → P b:=by
      intro a b ha hb haS hbS Hside hpa
      apply hpa.congr LaurentRay.vUnit Ω
      apply chart_sign_congr_through LaurentRay.vUnit Ω C _ _ F (n+1)
      intro j hj hjN m hm
      exact line_cell_signs S vR k a b haS hbS Hside (e m) (realRoot_mem e C (n+1) j hjN m hm)
    have hstep : ∀a∈events,0 < a → ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε → P (a+δ) → P (a-δ):=by
      intro a ha ha0
      exact wall_joint_induction Ω C e he B hB hcomp L hdeg n d r hd hr F ih k Hk a ha
    have HK : RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C (k.toAddMonoidHom.comp e) F).val:=by
      have HH:=descend events P hstart hcell hstep 0 (le_refl 0) h0
      simpa only [P,zero_smul,add_zero] using HH
    have Hchart:=chart_sign_congr_through LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (k.toAddMonoidHom.comp e) F (n+1) (by
        intro j hj hjN m hm
        have HS:=Hsign (e m) (realRoot_mem e C (n+1) j hjN m hm)
        refine ⟨HS.1,?_,HS.2⟩
        intro hh
        exact ((hg.2 j hj hjN m hm hh).eval (k.toAddMonoidHom.comp e)).2.1.mpr Hk.on_ray)
    exact HK.congr LaurentRay.vUnit Ω (fun j hj => (Hchart j hj).symm)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IsotropicLiteralPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter WallUnits
noncomputable section
variable {M J ι : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (l : Filter ι)
lemma SeriesConverges.inverse_adjoint
    {f : ι→PowerSeries (Torus LaurentRay.vUnit Ω)} {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hf : SeriesConverges LaurentRay.vUnit Ω l f F)
    (hfg : ∀i,SeriesGraded LaurentRay.vUnit Ω C (f i))
    (hF : SeriesGraded LaurentRay.vUnit Ω C F) (x : Torus LaurentRay.vUnit Ω) :
    SeriesConverges LaurentRay.vUnit Ω l (fun i=>invOfUnit (f i) 1*PowerSeries.C x*f i)
      (invOfUnit F 1*PowerSeries.C x*F) := by
  have H:=hf.inverse LaurentRay.vUnit Ω C l hfg hF
  have hi : ∀i,SeriesGraded LaurentRay.vUnit Ω C (invOfUnit (f i) 1):=
    fun i=>(hfg i).inverse LaurentRay.vUnit Ω C
  have hI:=hF.inverse LaurentRay.vUnit Ω C
  exact (H.mul_C LaurentRay.vUnit Ω C l hi hI x).mul_of_support LaurentRay.vUnit Ω l hf
    (fun n=>sumSupport (rootDegree_finite C n).toFinset x.support)
    (fun n=>(rootDegree_finite C n).toFinset)
    (fun i n=>(hi i).mul_C_support LaurentRay.vUnit Ω C x n)
    (fun i n=>rootGrade_support LaurentRay.vUnit Ω C n _ (hfg i n))
    (fun n=>hI.mul_C_support LaurentRay.vUnit Ω C x n)
    (fun n=>rootGrade_support LaurentRay.vUnit Ω C n _ (hF n))

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits LaurentPrecision
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ)
lemma positiveRayWithZero_isotropic (hΩ : ∀r,Ω r r=0) (r : M) :
    ∀p∈positiveRayWithZero r,∀q∈positiveRayWithZero r,Ω p q=0 := by
  intro p hp q hq
  rcases hp with rfl|hp
  · simp
  rcases hq with rfl|hq
  · simp
  exact hp.pair_zero Ω hq (hΩ r)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteWallCrossing
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits LaurentPrecision Filter RootTruncation
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma inverse_adjoint_coeff_congr (F G X : PowerSeries (Torus LaurentRay.vUnit Ω)) (N : ℕ)
    (h : ∀n≤N,coeff n F=coeff n G) :
    coeff N (invOfUnit F 1*X*F)=coeff N (invOfUnit G 1*X*G) := by
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact FormalLog.mul_coeff_congr _ _ _ _ j
      (fun k hk=>PowerSeriesAdjoint.inverse_coeff_congr F G j
        (fun t ht=>h t (ht.trans hj)) k hk) (fun _ _=>rfl)
  · exact h
lemma cut_adjoint_coeff (F X : PowerSeries (Torus LaurentRay.vUnit Ω)) (N n : ℕ) (hn : n≤N) :
    coeff n (PowerSeriesAdjoint.adjoint (cut N F) X)=coeff n (PowerSeriesAdjoint.adjoint F X) :=
  PowerSeriesAdjoint.adjoint_coeff_congr _ _ _ _ n
    (fun j hj=>by rw [coeff_cut,ite_eq_left (hj.trans hn)]) (fun _ _=>rfl)
lemma cut_inverse_adjoint_coeff (F X : PowerSeries (Torus LaurentRay.vUnit Ω)) (N n : ℕ) (hn : n≤N) :
    coeff n (invOfUnit (cut N F) 1*X*cut N F)=coeff n (invOfUnit F 1*X*F) :=
  inverse_adjoint_coeff_congr Ω _ _ _ n (fun j hj=>by rw [coeff_cut,ite_eq_left (hj.trans hn)])
lemma rootClosed_isotropic_adjoint (V : AddSubmonoid M) (hΩ : ∀p,Ω p p=0)
    (hV : ∀p∈V,∀q∈V,Ω p q=0) {N : ℕ} {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (fun p=>p∈V)) F) :
    (∀m,(∀p∈V,0≤Ω p m) → ∀n≤N,TorusPositive Ω
      (coeff n (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1))) ∧
    (∀m,(∀p∈V,Ω p m≤0) → ∀n≤N,TorusPositive Ω
      (coeff n (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F))) := by
  let g:=rootApprox LaurentRay.vUnit Ω hF
  have hg:=rootApprox_converges LaurentRay.vUnit Ω hF
  have hgg : ∀T,SeriesGraded LaurentRay.vUnit Ω C (cut N (g T)):=
    fun T=>(literalRootProducts_graded Ω C _ (rootApprox_mem LaurentRay.vUnit Ω hF T)).cut LaurentRay.vUnit Ω C N
  have hFG : SeriesGraded LaurentRay.vUnit Ω C (cut N F):=by
    apply hF.graded Ω C
    rintro G ⟨G',hG,rfl⟩
    exact (literalRootProducts_graded Ω C _ hG).cut LaurentRay.vUnit Ω C N
  have hp:=fun T=>literal_isotropic_adjoint Ω C V hΩ hV (rootApprox_mem LaurentRay.vUnit Ω hF T)
  constructor
  · intro m hm n hn r
    have H:=hg.adjoint LaurentRay.vUnit Ω C Filter.atTop hgg hFG (Torus.X LaurentRay.vUnit Ω m)
    have he : ∀G,coeff n (cut N G*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit (cut N G) 1)=
        coeff n (G*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit G 1):=
      fun G=>cut_adjoint_coeff Ω G _ N n hn
    have Hn:=H n r
    simp only [he] at Hn
    exact LaurentPositive.of_converges Filter.atTop Hn (Eventually.of_forall (fun T=>(hp T).1 m hm n r))
  · intro m hm n hn r
    have H:=hg.inverse_adjoint Ω C Filter.atTop hgg hFG (Torus.X LaurentRay.vUnit Ω m)
    have he:=fun G=>cut_inverse_adjoint_coeff Ω G (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)) N n hn
    have Hn:=H n r
    simp only [he] at Hn
    exact LaurentPositive.of_converges Filter.atTop Hn (Eventually.of_forall (fun T=>(hp T).2 m hm n r))
lemma rootClosed_ray_adjoint (hΩ : ∀p,Ω p p=0) (r : M)
    {N : ℕ} {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r)) F) :
    (∀m,0≤Ω r m → ∀n≤N,TorusPositive Ω
      (coeff n (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1))) ∧
    (∀m,Ω r m≤0 → ∀n≤N,TorusPositive Ω
      (coeff n (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F))) := by
  have H:=rootClosed_isotropic_adjoint Ω C (positiveRayWithZero r) hΩ
    (positiveRayWithZero_isotropic Ω hΩ r)
    (hF.mono LaurentRay.vUnit Ω (literalRootProducts_allowed_mono Ω C _ _ (fun n hn p hr hp=>Or.inr hp)))
  constructor
  · intro m hm
    apply H.1 m
    intro p hp
    rcases hp with rfl|hp
    · simp
    exact hp.pair_nonneg Ω (OnPositiveRay.refl m) hm
  · intro m hm
    apply H.2 m
    intro p hp
    rcases hp with rfl|hp
    · simp
    have he:=hp.eval (incomingCovector Ω m)
    by_contra hx
    have hp0 : (0:ℝ)<Ω p m:=by exact_mod_cast (lt_of_not_ge hx)
    have hr0:=he.1.mp hp0
    change (0:ℝ)<Ω r m at hr0
    have hr1 : (Ω r m:ℝ)≤0:=by exact_mod_cast hm
    linarith
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint LaurentPositive WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (hΩ : ∀m,Ω m m=0)
include hΩ in
lemma ray_charge_through (p : M) (F : CompletedPositive LaurentRay.vUnit Ω C) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,coeff n F.val m≠0 → OnPositiveRay p m) :
    ∀n≤N,coeff n F.val∈chargeGrade LaurentRay.vUnit Ω (Ω p) 0 := by
  intro n hn
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff,F.property.1]
    exact chargeGrade_one LaurentRay.vUnit Ω (Ω p)
  | succ n =>
    intro m hm
    by_contra hx
    exact hm ((OnPositiveRay.refl p).pair_zero Ω (hs _ (by omega) hn m hx) (hΩ p))
include hΩ in
lemma ray_increment_positive (p r : M) (F : CompletedPositive LaurentRay.vUnit Ω C)
    (X : PowerSeries (Torus LaurentRay.vUnit Ω)) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,coeff n F.val m≠0 → OnPositiveRay p m)
    (hF : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay p)) F.val)
    (hX : ∀j<N,TorusPositive Ω (coeff j X)) :
    (0≤Ω p r → Positive (coeff N (adjoint F.val X) r-coeff N X r)) ∧
    (Ω p r≤0 → Positive (coeff N (adjoint (invOfUnit F.val 1) X) r-coeff N X r)) := by
  have hq:=ray_charge_through Ω C hΩ p F N hs
  have hp:=rootClosed_ray_adjoint Ω C hΩ p hF
  constructor
  · intro hr
    apply adjoint_increment_positive Ω F.val X (Ω p) N r F.property.1 hq hX
    intro m hm j hj
    exact (hp.1 m (by rw [hm]; exact hr) j hj) r
  · intro hr
    apply adjoint_increment_positive Ω (invOfUnit F.val 1) X (Ω p) N r (by simp)
      (chargeGrade_inverse LaurentRay.vUnit Ω (Ω p) F.val N hq) hX
    intro m hm j hj
    rw [adjoint_inverse F.val _ F.property.1]
    exact (hp.2 m (by rw [hm]; exact hr) j hj) r
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionRayTransition
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma section_ray_positive_side (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (p : M) (h k H : M →+ ℝ)
    (hg : RayGeneric C N p h) (hkp : 0<k p)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (sectionValue v Ω C F H X)=coeff n (sectionValue v Ω C F h X) := by
  have HD:=RayGeneric.ray_supported v Ω C hg F
  have Hneg:=chartNegative_of_positive_through v Ω C k (chartZero v Ω C h F) N (by
    intro n hn m hm
    exact ((by_contra fun hr=>hm (HD (n+1) (by omega) hn m hr) : OnPositiveRay p m).eval k).1.mpr hkp)
  intro n hn
  rw [section_refinement_through v Ω C h k H F X N hs n hn]
  have HE:=adjoint_coeff_congr (chartNegative v Ω C k (chartZero v Ω C h F)).val 1
    (sectionValue v Ω C F h X) (sectionValue v Ω C F h X) n
    (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)
  rw [HE,adjoint_one]
lemma section_ray_negative_side (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (p : M) (h k H : M →+ ℝ)
    (hg : RayGeneric C N p h) (hkp : k p<0)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (sectionValue v Ω C F H X)=
      coeff n (adjoint (chartZero v Ω C h F).val (sectionValue v Ω C F h X)) := by
  have HD:=RayGeneric.ray_supported v Ω C hg F
  have Hneg:=chartNegative_of_negative_through v Ω C k (chartZero v Ω C h F) N (by
    intro n hn m hm
    exact ((by_contra fun hr=>hm (HD (n+1) (by omega) hn m hr) : OnPositiveRay p m).eval k).2.2.mpr hkp)
  intro n hn
  rw [section_refinement_through v Ω C h k H F X N hs n hn]
  exact adjoint_coeff_congr _ _ _ _ n (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)
lemma section_ray_crossing (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (p : M) (h k Hplus Hminus : M →+ ℝ)
    (hg : RayGeneric C N p h)
    (hsplus : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k Hplus m)
    (hsminus : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h (-k) Hminus m) :
    (0<k p → ∀n≤N,coeff n (sectionValue v Ω C F Hminus X)=
      coeff n (adjoint (chartZero v Ω C h F).val (sectionValue v Ω C F Hplus X))) ∧
    (k p<0 → ∀n≤N,coeff n (sectionValue v Ω C F Hminus X)=
      coeff n (adjoint (invOfUnit (chartZero v Ω C h F).val 1) (sectionValue v Ω C F Hplus X))) := by
  constructor
  · intro hp n hn
    rw [section_ray_negative_side v Ω C F X N p h (-k) Hminus hg (by simpa using neg_neg_of_pos hp) hsminus n hn]
    exact adjoint_coeff_congr _ _ _ _ n (fun _ _=>rfl)
      (fun j hj=>(section_ray_positive_side v Ω C F X N p h k Hplus hg hp hsplus j (hj.trans hn)).symm)
  · intro hp n hn
    rw [section_ray_positive_side v Ω C F X N p h (-k) Hminus hg (by simpa using neg_pos.mpr hp) hsminus n hn]
    exact (adjoint_inverse_coeff _ _ _ (chartZero v Ω C h F).property.1 n
      (fun j hj=>section_ray_negative_side v Ω C F X N p h k Hplus hg hp hsplus j (hj.trans hn))).symm
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry PowerSeriesSplit PowerSeriesAdjoint
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
lemma section_line_zero_not_event (N : ℕ) (v k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 v k) :
    (0:ℝ)∉lineEvents (realRootsThrough e C N) v k := by
  intro hh
  obtain ⟨s,hs,hv,hs0⟩:=(mem_lineEvents_iff _ _ _ _).mp hh
  apply H.avoid s hs _
  · simpa only [zero_smul,add_zero] using hs0
  · simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using
      (show s≠0 from fun h=>hv (by rw [h,map_zero]))
lemma line_covector_add (v k : Module.Dual ℝ E) (a δ : ℝ) :
    ((k+(a+δ) • v).toAddMonoidHom.comp e)=
      (k+a • v).toAddMonoidHom.comp e+δ • (v.toAddMonoidHom.comp e) := by
  ext m
  change k (e m)+((a+δ)*v (e m))=(k (e m)+a*v (e m))+δ*v (e m)
  ring
lemma line_covector_sub (v k : Module.Dual ℝ E) (a δ : ℝ) :
    ((k+(a-δ) • v).toAddMonoidHom.comp e)=
      (k+a • v).toAddMonoidHom.comp e+δ • (-(v.toAddMonoidHom.comp e)) := by
  ext m
  change k (e m)+((a-δ)*v (e m))=(k (e m)+a*v (e m))+δ*(-v (e m))
  ring
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionGenericPerturbation
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (L : Module.Dual ℝ E)
variable (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hdeg in
lemma section_positive_perturbation (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (h : Module.Dual ℝ E) :
    ∃k : Module.Dual ℝ E,ChamberGeneric C N (k.toAddMonoidHom.comp e) ∧
      ∀n≤N,coeff n (sectionValue v Ω C F (k.toAddMonoidHom.comp e) X)=
        coeff n (sectionValue v Ω C F (h.toAddMonoidHom.comp e) X) := by
  let hM:=h.toAddMonoidHom.comp e
  let lM:=L.toAddMonoidHom.comp e
  obtain ⟨ε,hε,Hε⟩:=root_lex_epsilon C N hM lM
  let δ:=ε/2
  have hd : 0<δ:=by dsimp [δ] <;> linarith
  have hdε : δ<ε:=by dsimp [δ] <;> linarith
  have hk : (h+δ • L).toAddMonoidHom.comp e=hM+δ • lM:=by ext m; rfl
  refine ⟨h+δ • L,?_,?_⟩
  · rw [hk]
    intro n hn hnN m hm
    have HH:=Hε δ hd hdε n hnN m hm
    have hlpos : 0<lM m:=by change 0<L (e m); rw [hdeg n m hm]; exact_mod_cast hn
    rcases lt_trichotomy 0 (hM m) with hp|hz|hmn
    · exact ne_of_gt (HH.1 hp)
    · exact ne_of_gt ((HH.2.2 hz.symm).1 hlpos)
    · exact ne_of_lt (HH.2.1 hmn)
  · rw [hk]
    have Hneg:=chartNegative_of_positive_through v Ω C lM (chartZero v Ω C hM F) N (by
      intro n hn m hm
      change 0<L (e m)
      rw [hdeg (n+1) m (chart_root_of_ne v Ω C _ _ m hm)]
      positivity)
    intro n hn
    rw [section_refinement_through v Ω C hM lM _ F X N (Hε δ hd hdε) n hn]
    have HH:=adjoint_coeff_congr (chartNegative v Ω C lM (chartZero v Ω C hM F)).val 1
      (sectionValue v Ω C F hM X) (sectionValue v Ω C F hM X) n
      (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)
    rw [HH,adjoint_one]
include hdeg in
lemma section_generic_offset (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (h dir : Module.Dual ℝ E) :
    ∃k : Module.Dual ℝ E,GenericOffset (realRootsThrough e C N) 0 dir k ∧
      ∀n≤N,coeff n (sectionValue v Ω C F (k.toAddMonoidHom.comp e) X)=
        coeff n (sectionValue v Ω C F (h.toAddMonoidHom.comp e) X) := by
  obtain ⟨h',hgen,heq⟩:=section_positive_perturbation v Ω C e L hdeg F X N h
  obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset (realRootsThrough e C N) 0 dir h' (map_zero h')
  refine ⟨k,Hk,?_⟩
  have HH:=section_sign_congr_through v Ω C (h'.toAddMonoidHom.comp e)
    (k.toAddMonoidHom.comp e) F X N (by
      intro n hn hnN m hm
      have HS:=Hsign (e m) (realRoot_mem e C N n hnN m hm)
      exact ⟨HS.1,fun hh=>False.elim (hgen n hn hnN m hm hh),HS.2⟩)
  exact fun n hn=>(HH n hn).symm.trans (heq n hn)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionIncoming
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
attribute [local instance] Classical.propDecidable
variable (F : CompletedPositive v Ω C) (b : M)

local instance sectionIncomingAddCommGroup_r40199e_1 : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance sectionIncomingAddGroup_r40199e_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance sectionIncomingSub_r40199e_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma sectionIncoming_apply (n : ℕ) (X : PowerSeries (Torus v Ω)) (m : M) :
    sectionIncoming v Ω C F b n X m=if HasRootDegree C n (m-b) then
      (coeff n (sectionValue v Ω C F (incomingCovector Ω m) X)) m else 0 := rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularCommutativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry LaurentPositive WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
lemma section_line_step (N : ℕ) (r : M) (F : CompletedPositive LaurentRay.vUnit Ω C)
    (walls : WallsPositiveThrough Ω C e N F) (X : PowerSeries (Torus LaurentRay.vUnit Ω))
    (ih : ∀j<N,∀h : Module.Dual ℝ E,TorusPositive Ω (coeff j (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X)))
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 (B.flip (e r)) k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C N) (B.flip (e r)) k) :
    ∃ε>0,∀δ : ℝ,0<δ → δ<ε →
      Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e) X) r) →
      Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e) X) r) := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  obtain ⟨p,d,hd,hdN,hp,hv,hgen⟩:=section_event_ray C e he L hdeg N (B.flip (e r)) k H a ha
  let h:=(k+a • B.flip (e r)).toAddMonoidHom.comp e
  let dir:=(B.flip (e r)).toAddMonoidHom.comp e
  obtain ⟨εp,hεp,Hεp⟩:=root_lex_epsilon C N h dir
  obtain ⟨εm,hεm,Hεm⟩:=root_lex_epsilon C N h (-dir)
  refine ⟨min εp εm,lt_min hεp hεm,?_⟩
  intro δ hδ hδε hplus
  have hδp:=lt_of_lt_of_le hδε (min_le_left _ _)
  have hδm:=lt_of_lt_of_le hδε (min_le_right _ _)
  let hpM:=(k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e
  let hmM:=(k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e
  have HC:=section_ray_crossing LaurentRay.vUnit Ω C F X N p h dir hpM hmM hgen
    (by simpa only [hpM,line_covector_add] using Hεp δ hδ hδp)
    (by simpa only [hmM,line_covector_sub] using Hεm δ hδ hδm)
  have HS : ∀n,0<n → n≤N → ∀m,coeff n (chartZero LaurentRay.vUnit Ω C h F).val m≠0 → OnPositiveRay p m:=by
    intro n hn hnN m hm
    by_contra hh
    exact hm ((hgen.ray_supported LaurentRay.vUnit Ω C F n hn hnN) m hh)
  have HI:=ray_increment_positive Ω C hΩ p r (chartZero LaurentRay.vUnit Ω C h F)
    (sectionValue LaurentRay.vUnit Ω C F hpM X) N HS
    (walls p d hd hp (k+a • B.flip (e r)) hgen)
    (fun j hj=>ih j hj (k+(a+δ) • B.flip (e r)))
  have Hpair : dir p=(Ω p r:ℝ):=hcomp p r
  have Hne : dir p≠0:=hv
  rcases lt_or_gt_of_ne Hne with hneg|hpos
  · have Hinc:=HI.2 (by exact_mod_cast (le_of_lt (Hpair ▸ hneg)))
    rw [←HC.2 hneg N le_rfl] at Hinc
    have HA:=Hinc.add hplus
    simpa only [hpM,hmM,sub_add_cancel] using HA
  · have Hinc:=HI.1 (by exact_mod_cast (le_of_lt (Hpair ▸ hpos)))
    rw [←HC.1 hpos N le_rfl] at Hinc
    have HA:=Hinc.add hplus
    simpa only [hpM,hmM,sub_add_cancel] using HA
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

theorem positive_sections_oai (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) (b : M)
    (X : PowerSeries (Torus LaurentRay.vUnit Ω)) (hX : ShiftGraded LaurentRay.vUnit Ω C b X)
    (hinc : ∀n,TorusPositive Ω (sectionIncoming LaurentRay.vUnit Ω C F b n X)) :
    ∀N,∀h : Module.Dual ℝ E,TorusPositive Ω (coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X)) := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  have walls:=positive_walls_through Ω C e he B hB hcomp L hdeg F incoming
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro h r
    obtain ⟨k,Hk,Heq⟩:=section_generic_offset LaurentRay.vUnit Ω C e L hdeg F X N h (B.flip (e r))
    rw [←Heq N le_rfl]
    let dir:=B.flip (e r)
    let S:=realRootsThrough e C N
    let events:=lineEvents S dir k
    let P (a : ℝ):=Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+a • dir).toAddMonoidHom.comp e) X) r)
    have h0 : (0:ℝ)∉events:=section_line_zero_not_event C e N dir k Hk
    have hstart : ∃a,0≤a ∧ (∀z∈events,z<a) ∧ P a:=by
      obtain ⟨a,ha,Hbound⟩:=finite_upper_bound events
      refine ⟨a,ha.le,Hbound,?_⟩
      change Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+a • dir).toAddMonoidHom.comp e) X) r)
      have Hpert:=section_incoming_perturbation LaurentRay.vUnit Ω C hΩ r
        (k.toAddMonoidHom.comp e) ((k+a • dir).toAddMonoidHom.comp e) F X N (by
          intro n hn m hm
          have HH:=far_line_lex S dir k a Hbound (e m) (realRoot_mem e C N n hn m hm)
          simp only [dir,LinearMap.flip_apply,hcomp] at HH
          exact HH)
      rw [Hpert]
      by_cases hr : HasRootDegree C N (r-b)
      · have HH:=hinc N r
        rw [sectionIncoming_apply,ite_eq_left hr] at HH
        exact HH
      · rw [(hX.sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω r)) N r hr]
        exact positive_zero
    have hcell : ∀a a',0≤a → 0≤a' → a∉events → a'∉events →
        (∀z∈events,a<z ↔ a'<z) → P a → P a':=by
      intro a a' ha ha' hna hna' Hside hpa
      have HH:=section_sign_congr_through LaurentRay.vUnit Ω C
        ((k+a • dir).toAddMonoidHom.comp e) ((k+a' • dir).toAddMonoidHom.comp e) F X N (by
          intro n hn hnN m hm
          exact line_cell_signs S dir k a a' hna hna' Hside (e m) (realRoot_mem e C N n hnN m hm))
      change Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+a' • dir).toAddMonoidHom.comp e) X) r)
      rw [←HH N le_rfl]
      exact hpa
    have hstep : ∀a∈events,0<a → ∃ε>0,∀δ : ℝ,0<δ → δ<ε → P (a+δ) → P (a-δ):=by
      intro a ha ha0
      exact section_line_step Ω C e he B hB hcomp L hdeg N r F (walls N) X ih k Hk a ha
    have HH:=descend events P hstart hcell hstep 0 (le_refl 0) h0
    simpa only [P,zero_smul,add_zero] using HH
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.positive_sections_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.positive_sections_oai.{u_1, u_2, u_3}
