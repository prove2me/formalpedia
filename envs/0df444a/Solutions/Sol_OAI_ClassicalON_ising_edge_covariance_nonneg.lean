-- Prove2me | solution 1 for OAI.ClassicalON.ising_edge_covariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:55:11.654426+00:00
-- url     : https://prove2.me/submissions/9fcf1941-4f61-4cad-9745-56a4d55e20da

import Mathlib
import Definitions.Def_OAIQWCO002

section
-- module Solutions.OAIQW_ClassicalON.AssociationCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ClassicalON

section CompactIntegral
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} [IsFiniteMeasure μ]

theorem compact_integrable {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem compact_integral_pos [IsProbabilityMeasure μ] {w : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) : 0<∫ x,w x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) (compact_integrable hw)).2
  have he : Function.support w=univ := by ext x; simp [Function.mem_support,(hp x).ne']
  rw [he,measure_univ]
  exact zero_lt_one

end CompactIntegral

section Weighted
variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
  [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {w : X → ℝ}
  (hw : Continuous w) (hp : ∀ x,0<w x)

include hw hp

theorem weightedMean_inequality_iff {f g : X → ℝ} :
    weightedMean μ w f * weightedMean μ w g ≤ weightedMean μ w (fun x => f x*g x) ↔
    (∫ x,w x*f x ∂μ)*(∫ x,w x*g x ∂μ) ≤ (∫ x,w x ∂μ)*(∫ x,w x*(f x*g x) ∂μ) := by
  unfold weightedMean
  have hm := compact_integral_pos (μ := μ) hw hp
  rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos hm hm) hm]
  constructor <;> intro h <;> nlinarith

end Weighted

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.IsingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

variable {V : Type uV} [Fintype V]

omit [Fintype V] in
theorem isingUW_moment (k l : ℕ) :
    0≤∫ t : Bool×Bool,isingU t^k*isingW t^l ∂signLaw.prod signLaw := by
  rw [integral_prod _ (compact_integrable (by fun_prop))]
  simp only [signLaw,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
    smul_eq_mul,integral_count,Fintype.sum_bool]
  simp only [isingU,isingW,signValue,Bool.false_eq_true,ite_false,ite_true]
  norm_num
  by_cases hk : k=0 <;> by_cases hl : l=0
  · subst k; subst l; norm_num
  · subst k
    simp only [pow_zero,one_mul,zero_pow hl]
    have h' : -1≤(-1 : ℝ)^l := by
      simpa only [abs_pow,abs_neg,abs_one,one_pow] using neg_abs_le ((-1 : ℝ)^l)
    nlinarith
  · subst l
    simp only [pow_zero,mul_one,zero_pow hk]
    have h' : -1≤(-1 : ℝ)^k := by
      simpa only [abs_pow,abs_neg,abs_one,one_pow] using neg_abs_le ((-1 : ℝ)^k)
    nlinarith
  · simp [zero_pow hk,zero_pow hl]

omit [Fintype V] in
theorem isingUW_product_moment (l : List Bool) :
    0≤∫ t : Bool×Bool,(l.map (fun b => if b then isingU t else isingW t)).prod
      ∂signLaw.prod signLaw := by
  have he (t : Bool×Bool) :
      (l.map (fun b => if b then isingU t else isingW t)).prod =
      isingU t^(l.count true)*isingW t^(l.count false) := by
    induction l with
    | nil => simp
    | cons b l ih => cases b <;> simp [ih,pow_succ] <;> ring
  simp_rw [he]
  exact isingUW_moment _ _

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ExpMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

theorem real_hasSum_exp (x : ℝ) : HasSum (fun k : ℕ => x^k/(k.factorial : ℝ)) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem hasSum_integral_mul_exp {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h) :
    HasSum (fun k : ℕ => (∫ x,f x*h x^k ∂μ)/(k.factorial : ℝ))
      (∫ x,f x*Real.exp (h x) ∂μ) := by
  let F : ℕ → X → ℝ := fun k x => f x*(h x^k/(k.factorial : ℝ))
  let B : ℕ → X → ℝ := fun k x => ‖f x‖*(‖h x‖^k/(k.factorial : ℝ))
  have hF : ∀ k,AEStronglyMeasurable (F k) μ := by
    intro k
    exact (compact_integrable (show Continuous (F k) from (hf.mul ((hh.pow k).div_const _)))).aestronglyMeasurable
  have hB : ∀ k,∀ᵐ x ∂μ,‖F k x‖≤B k x := by
    intro k
    filter_upwards with x
    simp only [F,B,norm_mul,norm_div,norm_pow,Real.norm_natCast]
    exact le_rfl
  have hS : ∀ᵐ x ∂μ,Summable (fun k => B k x) := by
    filter_upwards with x
    exact ((real_hasSum_exp ‖h x‖).mul_left ‖f x‖).summable
  have hI : Integrable (fun x => ∑' k,B k x) μ := by
    have he : (fun x => ∑' k : ℕ,B k x) = (fun x => ‖f x‖*Real.exp ‖h x‖) := by
      funext x; exact ((real_hasSum_exp ‖h x‖).mul_left ‖f x‖).tsum_eq
    rw [he]
    exact compact_integrable (hf.norm.mul hh.norm.rexp)
  have hL : ∀ᵐ x ∂μ,HasSum (fun k => F k x) (f x*Real.exp (h x)) := by
    filter_upwards with x
    exact (real_hasSum_exp (h x)).mul_left (f x)
  have ht := hasSum_integral_of_dominated_convergence B hF hB hS hI hL
  simpa only [F,← mul_div_assoc,integral_div] using ht

theorem integral_mul_exp_nonneg_of_moments {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hm : ∀ k : ℕ,0≤∫ x,f x*h x^k ∂μ) : 0≤∫ x,f x*Real.exp (h x) ∂μ :=
  (hasSum_integral_mul_exp μ hf hh).nonneg (fun k => div_nonneg (hm k) (Nat.cast_nonneg _))

theorem integral_mul_sum_exp_nonneg {E : Type uE} [Fintype E]
    {f : X → ℝ} {a : E → X → ℝ} (hf : Continuous f)
    (ha : ∀ e,Continuous (a e)) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (hm : ∀ (k : ℕ) (p : Fin k → E),0≤∫ x,f x*∏ i,a (p i) x ∂μ) :
    0≤∫ x,f x*Real.exp (∑ e,b e*a e x) ∂μ := by
  apply integral_mul_exp_nonneg_of_moments μ hf (by fun_prop)
  intro k
  simp_rw [Fintype.sum_pow,Finset.mul_sum]
  rw [integral_finsetSum _ (fun p _ => compact_integrable (by fun_prop))]
  apply Finset.sum_nonneg
  intro p _
  have he : (fun x => f x*∏ i,b (p i)*a (p i) x)=
      (fun x => (∏ i,b (p i))*(f x*∏ i,a (p i) x)) := by
    funext x; rw [Finset.prod_mul_distrib]; ring
  rw [he,integral_const_mul]
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => hb (p i))) (hm k p)

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.MomentCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uJ uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {X : Type uX} {I : Type uI} {a : I → X → ℝ}

theorem momentCone_const {c : ℝ} (hc : 0≤c) : MomentCone a (fun _ => c) := by
  refine ⟨1,fun _ => c,fun _ => [],fun _ => hc,?_⟩
  intro x; simp

theorem momentCone_coordinate (i : I) : MomentCone a (a i) := by
  refine ⟨1,fun _ => 1,fun _ => [i],fun _ => by norm_num,?_⟩
  intro x; simp

theorem momentCone_add {f g : X → ℝ} (hf : MomentCone a f) (hg : MomentCone a g) :
    MomentCone a (fun x => f x+g x) := by
  rcases hf with ⟨k,c,p,hc,hf⟩
  rcases hg with ⟨l,d,q,hd,hg⟩
  refine ⟨k+l,Fin.append c d,Fin.append p q,?_,?_⟩
  · intro j; cases j using Fin.addCases <;> simp_all
  · intro x
    change f x+g x=_
    rw [hf,hg,Fin.sum_univ_add]
    simp

theorem momentCone_mul {f g : X → ℝ} (hf : MomentCone a f) (hg : MomentCone a g) :
    MomentCone a (fun x => f x*g x) := by
  classical
  rcases hf with ⟨k,c,p,hc,hf⟩
  rcases hg with ⟨l,d,q,hd,hg⟩
  let e := (finProdFinEquiv : Fin k × Fin l ≃ Fin (k*l)).symm
  refine ⟨k*l,fun j => c (e j).1*d (e j).2,
    fun j => p (e j).1 ++ q (e j).2,
    fun j => mul_nonneg (hc _) (hd _),?_⟩
  intro x
  simp only [List.map_append,List.prod_append]
  rw [Equiv.sum_comp e (fun z : Fin k × Fin l => c z.1*d z.2*
    ((List.map (fun i => a i x) (p z.1)).prod*(List.map (fun i => a i x) (q z.2)).prod))]
  simp only [Fintype.sum_prod_type]
  rw [hf,hg,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem momentCone_finsetProd {J : Type uJ} (s : Finset J) (f : J → X → ℝ)
    (hf : ∀ j∈s,MomentCone a (f j)) : MomentCone a (fun x => ∏ j∈s,f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (momentCone_const (a := a) (by norm_num : (0 : ℝ)≤1))
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      momentCone_mul (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

section Integral
variable [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem momentCone_integral_nonneg (ha : ∀ i,Continuous (a i))
    (hm : ∀ (k : ℕ) (p : Fin k → I),0≤∫ x,∏ i,a (p i) x ∂μ)
    {f : X → ℝ} (hf : MomentCone a f) : 0≤∫ x,f x ∂μ := by
  rcases hf with ⟨k,c,p,hc,hf⟩
  simp_rw [hf]
  have hp : ∀ l : List I,Continuous (fun x => (l.map (fun i => a i x)).prod) := by
    intro l
    induction l with
    | nil => simpa using (continuous_const : Continuous (fun _ : X => (1 : ℝ)))
    | cons i l ih =>
      simp only [List.map_cons,List.prod_cons]
      apply Continuous.mul
      · exact ha i
      · exact ih
  have hI (j : Fin k) : Integrable (fun x => c j*(List.map (fun i => a i x) (p j)).prod) μ :=
    compact_integrable (by
      apply Continuous.mul
      · exact continuous_const
      · exact hp (p j))
  rw [integral_finsetSum _ (fun j _ => hI j)]
  apply Finset.sum_nonneg
  intro j _
  rw [integral_const_mul]
  apply mul_nonneg (hc j)
  have he (x : X) : (List.map (fun i => a i x) (p j)).prod =
      ∏ i : Fin (p j).length,a ((p j).get i) x := by
    have hh := List.ofFn_comp' (List.get (p j)) (fun i => a i x)
    rw [List.ofFn_get] at hh
    rw [← hh,List.prod_ofFn]
  simp_rw [he]
  exact hm (p j).length (fun i => (p j).get i)

end Integral
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProductMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {I : Type uI} {X : Type uX} [Fintype V] [DecidableEq V]

theorem site_grouping (a : I → X → ℝ) (l : List (V×I)) (x : V → X) :
    (l.map (fun p => a p.2 (x p.1))).prod =
      ∏ v,((retainedIndices v l).map (fun i => a i (x v))).prod := by
  induction l with
  | nil => simp [retainedIndices]
  | cons p l ih =>
    have hv (v : V) :
        ((retainedIndices v (p::l)).map (fun i => a i (x v))).prod =
        (if p.1=v then a p.2 (x p.1) else 1)*
          ((retainedIndices v l).map (fun i => a i (x v))).prod := by
      by_cases h : p.1=v
      · subst v; simp [retainedIndices]
      · simp [retainedIndices,h]
    simp only [List.map_cons,List.prod_cons,ih,hv,Finset.prod_mul_distrib]
    congr 1
    simp

theorem independent_moments_nonneg [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (a : I → X → ℝ)
    (hm : ∀ l : List I,0≤∫ x,(l.map (fun i => a i x)).prod ∂μ)
    (l : List (V×I)) :
    0≤∫ x : V → X,(l.map (fun p => a p.2 (x p.1))).prod ∂Measure.pi (fun _ => μ) := by
  simp_rw [site_grouping a l]
  rw [integral_fintype_prod_eq_prod (fun v x =>
    (List.map (fun i => a i x) (retainedIndices v l)).prod)]
  exact Finset.prod_nonneg (fun v _ => hm (retainedIndices v l))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.GibbsCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open MeasureTheory
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem doubled_covariance_identity {w f g : X → ℝ}
    (hw : Continuous w) (hf : Continuous f) (hg : Continuous g) :
    (∫ p : X×X,w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2) ∂μ.prod μ) =
      2*((∫ x,w x ∂μ)*(∫ x,w x*(f x*g x) ∂μ)-
        (∫ x,w x*f x ∂μ)*(∫ x,w x*g x ∂μ)) := by
  have he : (fun p : X×X => w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2)) =
      (fun p : X×X => (w p.1*(f p.1*g p.1)*w p.2+w p.1*(w p.2*(f p.2*g p.2)))-
        (w p.1*f p.1*(w p.2*g p.2)+w p.1*g p.1*(w p.2*f p.2))) := by
    funext p; ring
  rw [he,integral_sub (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop)),
    integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop)),
    integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop))]
  rw [integral_prod_mul (fun x => w x*(f x*g x)) w,
    integral_prod_mul w (fun x => w x*(f x*g x)),
    integral_prod_mul (fun x => w x*f x) (fun x => w x*g x),
    integral_prod_mul (fun x => w x*g x) (fun x => w x*f x)]
  ring

theorem covariance_nonneg_of_doubled {w f g : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) (hf : Continuous f) (hg : Continuous g)
    (h : 0≤∫ p : X×X,w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2) ∂μ.prod μ) :
    weightedMean μ w f*weightedMean μ w g≤weightedMean μ w (fun x => f x*g x) := by
  rw [doubled_covariance_identity μ hw hf hg] at h
  apply (weightedMean_inequality_iff hw hp).2
  linarith

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.IsingGinibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem isingDoubleEnergy_cone (left right : E → V) (e : E) :
    MomentCone isingDoubleVariable (isingDoubleEnergy left right e) := by
  exact momentCone_add
    (momentCone_mul (momentCone_coordinate (left e,true)) (momentCone_coordinate (right e,true)))
    (momentCone_mul (momentCone_coordinate (left e,false)) (momentCone_coordinate (right e,false)))

omit [Fintype V] [Fintype E] in
theorem isingDoubleDifference_cone (left right : E → V) (e : E) :
    MomentCone isingDoubleVariable (isingDoubleDifference left right e) := by
  exact momentCone_mul (momentCone_const (by norm_num : (0 : ℝ)≤2)) (momentCone_add
    (momentCone_mul (momentCone_coordinate (left e,true)) (momentCone_coordinate (right e,false)))
    (momentCone_mul (momentCone_coordinate (left e,false)) (momentCone_coordinate (right e,true))))

omit [Fintype E] in
theorem isingDoubleVariable_moments (k : ℕ) (p : Fin k → V×Bool) :
    0≤∫ z : V → Bool×Bool,∏ i,isingDoubleVariable (p i) z
      ∂Measure.pi (fun _ => signLaw.prod signLaw) := by
  classical
  have hh := independent_moments_nonneg (V := V) (signLaw.prod signLaw)
    (fun b t => if b then isingU t else isingW t) isingUW_product_moment (List.ofFn p)
  simpa only [isingDoubleVariable,List.map_ofFn,List.prod_ofFn,Function.comp_def] using hh

omit [Fintype V] [Fintype E] in
theorem isingDoubleEnergy_identity (left right : E → V) (e : E) (p : V → Bool×Bool) :
    isingEnergy left right e (fun v => (p v).1)+
      isingEnergy left right e (fun v => (p v).2)=2*isingDoubleEnergy left right e p := by
  unfold isingEnergy isingDoubleEnergy isingU isingW
  ring

omit [Fintype V] [Fintype E] in
theorem isingDoubleDifference_identity (left right : E → V) (e : E) (p : V → Bool×Bool) :
    isingEnergy left right e (fun v => (p v).1)-
      isingEnergy left right e (fun v => (p v).2)=isingDoubleDifference left right e p := by
  unfold isingEnergy isingDoubleDifference isingU isingW
  ring

theorem ising_edge_covariance_nonneg_oai (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (e f : E) :
    isingMean left right b (isingEnergy left right e)*
      isingMean left right b (isingEnergy left right f) ≤
    isingMean left right b (fun s => isingEnergy left right e s*isingEnergy left right f s) := by
  classical
  let T := isingEnergy left right
  let H := isingHamiltonian left right b
  let D := isingDoubleDifference left right
  let A := isingDoubleEnergy left right
  let μ := (isingReference (V := V)).prod (isingReference (V := V))
  let ν := Measure.pi (fun _ : V => signLaw.prod signLaw)
  let F : ((V → Bool)×(V → Bool)) → ℝ := fun p =>
    Real.exp (H p.1)*Real.exp (H p.2)*(T e p.1-T e p.2)*(T f p.1-T f p.2)
  apply covariance_nonneg_of_doubled isingReference (continuous_of_discreteTopology)
    (fun s => Real.exp_pos (H s)) continuous_of_discreteTopology continuous_of_discreteTopology
  change 0≤∫ p,F p ∂μ
  let h := measurePreserving_arrowProdEquivProdArrow Bool Bool V (fun _ => signLaw) (fun _ => signLaw)
  change 0≤∫ p,F p ∂(Measure.pi (fun _ : V => signLaw)).prod (Measure.pi (fun _ : V => signLaw))
  rw [← h.integral_comp' F]
  have he : (fun p => F (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool V p))=
      (fun p => (D e p*D f p)*Real.exp (∑ g,(2*b g)*A g p)) := by
    funext p
    change Real.exp (H (fun v => (p v).1))*Real.exp (H (fun v => (p v).2))*
      (T e (fun v => (p v).1)-T e (fun v => (p v).2))*
      (T f (fun v => (p v).1)-T f (fun v => (p v).2))=_
    rw [← Real.exp_add]
    have hH : H (fun v => (p v).1)+H (fun v => (p v).2)=∑ g,(2*b g)*A g p := by
      simp only [H,isingHamiltonian,← Finset.sum_add_distrib,← mul_add,isingDoubleEnergy_identity]
      apply Finset.sum_congr rfl; intro g _; change b g*(2*A g p)=(2*b g)*A g p; ring
    rw [hH]
    change Real.exp _*(isingEnergy _ _ _ _-isingEnergy _ _ _ _)*
      (isingEnergy _ _ _ _-isingEnergy _ _ _ _)=_
    rw [isingDoubleDifference_identity,isingDoubleDifference_identity]
    dsimp only [D]
    ring
  rw [he]
  apply integral_mul_sum_exp_nonneg ν continuous_of_discreteTopology
    (fun _ => continuous_of_discreteTopology) (fun g => 2*b g)
    (fun g => mul_nonneg (by norm_num) (hb g))
  intro k p
  apply momentCone_integral_nonneg ν (fun _ => continuous_of_discreteTopology)
    isingDoubleVariable_moments
  apply momentCone_mul
  · exact momentCone_mul (isingDoubleDifference_cone _ _ e) (isingDoubleDifference_cone _ _ f)
  · exact momentCone_finsetProd Finset.univ (fun i => A (p i))
      (fun i _ => isingDoubleEnergy_cone _ _ _)

end ClassicalON

end

end OAI
end

theorem solution.{uE, uV} : type_of% @OAI.ClassicalON.ising_edge_covariance_nonneg_oai.{uE, uV} := @OAI.ClassicalON.ising_edge_covariance_nonneg_oai.{uE, uV}
