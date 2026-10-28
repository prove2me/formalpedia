-- Prove2me | solution 1 for OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:02:20.360128+00:00
-- url     : https://prove2.me/submissions/e1265271-8d63-424d-9d6e-3ca5116885c6

import Mathlib
import Definitions.Def_OAIQ078B001

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_LocalProjectiveTopology
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceBorel _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory Module Metric TopologicalSpace
open scoped Classical Topology

namespace CriticalPercolation.LocalProjective
variable (K V : Type*) [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

lemma continuous_point : Continuous (point K V) := continuous_quot_mk
lemma openQuotient_point : IsOpenQuotientMap (point K V) :=
  MulAction.isOpenQuotientMap_quotientMk

variable {K V}
lemma point_eq_iff (v w : NZ V) : point K V v=point K V w ↔
    ∃ a : K, a • (w:V)=(v:V) := by
  constructor
  · intro he
    obtain ⟨a,ha⟩ := Quotient.exact he
    exact ⟨a,congrArg Subtype.val ha⟩
  · rintro ⟨a,ha⟩
    have hane : a≠0 := by intro he; rw [he,zero_smul] at ha; exact v.property ha.symm
    apply Quotient.sound
    exact ⟨Units.mk0 a hane,Subtype.ext ha⟩

lemma point_eq_iff_dependent (v w : NZ V) : point K V v=point K V w ↔
    ¬LinearIndependent K ![(v:V),(w:V)] := by
  rw [point_eq_iff,linearIndependent_fin2]
  change (∃ a : K, a • (w:V)=(v:V)) ↔ ¬((w:V)≠0 ∧ ∀ a : K, a • (w:V)≠(v:V))
  constructor
  · rintro ⟨a,ha⟩ h
    exact h.2 a ha
  · intro h
    by_contra hn
    exact h ⟨w.property,fun a ha => hn ⟨a,ha⟩⟩

instance spaceT2 [CompleteSpace K] : T2Space (Space K V) := by
  apply (t2Space_iff_of_isOpenQuotientMap (openQuotient_point K V)).mpr
  have hc : Continuous (fun z : NZ V × NZ V => ![(z.1:V),(z.2:V)]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  convert (isOpen_setOfPred_linearIndependent (𝕜:=K) (E:=V) (ι:=Fin 2)).isClosed_compl.preimage hc using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  exact point_eq_iff_dependent z.1 z.2

variable (K V)
instance spaceCompact [ProperSpace K] [FiniteDimensional K V] : CompactSpace (Space K V) := by
  let : ProperSpace V := FiniteDimensional.proper K V
  obtain ⟨c,hc⟩ := NormedField.exists_one_lt_norm K
  let r : ℝ := 1/‖c‖
  have hr : 0 < r := div_pos zero_lt_one (lt_trans zero_lt_one hc)
  let C : Set V := {v | r≤‖v‖ ∧ ‖v‖≤1}
  have hC : IsCompact C := by
    have he : C=Metric.closedBall (0:V) 1 ∩ {v | r≤‖v‖} := by
      ext v
      simp only [C,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right,and_comm]
    rw [he]
    exact (isCompact_closedBall (0:V) 1).inter_right (isClosed_le continuous_const continuous_norm)
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let f : C → NZ V := fun v => ⟨v,fun he => by
    have hh := v.property.1
    rw [he,norm_zero] at hh
    exact hr.not_ge hh⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  apply Function.Surjective.compactSpace ((continuous_point K V).comp hf)
  intro q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  obtain ⟨a,ha,hlt,hle,_⟩ := rescale_to_shell hc zero_lt_one (x:=(v:V)) v.property
  let w : C := ⟨a • (v:V),hle,hlt.le⟩
  refine ⟨w,(point_eq_iff (f w) v).mpr ⟨a,rfl⟩⟩

instance spaceMetrizable [ProperSpace K] [FiniteDimensional K V] :
    MetrizableSpace (Space K V) := inferInstance

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_PolynomialGrowthDescent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma hasPolynomialDegree_iff (d : ℕ) : HasPolynomialDegree A d ↔
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧
      Subgroup.closure (S : Set A)=⊤ ∧ HasDegree S d := by
  constructor
  · rintro ⟨S,hSf,h1,hsym,hgen,C,hC⟩
    refine ⟨hSf.toFinset,by simpa using h1,?_,by simpa using hgen,C,?_⟩
    · apply Finset.coe_injective
      simpa only [Finset.coe_inv,Set.Finite.coe_toFinset] using hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      refine ⟨n,hn,?_⟩
      have hb' : ((hSf.toFinset : Set A)^n).ncard ≤ C*n^d := by
        simpa only [Set.Finite.coe_toFinset] using hb
      simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb'
  · rintro ⟨S,h1,hsym,hgen,C,hC⟩
    refine ⟨S,S.finite_toSet,h1,?_,hgen,C,?_⟩
    · simpa only [Finset.coe_inv] using congrArg (fun T : Finset A => (T : Set A)) hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      exact ⟨n,hn,by simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb⟩

omit [DecidableEq A] in
lemma HasPolynomialDegree.fg {d : ℕ} (h : HasPolynomialDegree A d) : Group.FG A := by
  obtain ⟨S,hS,_,_,hgen,_⟩ := h
  exact Group.fg_iff.mpr ⟨S,hgen,hS⟩

universe u

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_RealSparseDoubling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace CriticalPercolation.HarmonicAnalysis

lemma sparse_real_doubling (f : ℕ → ℝ) (hf : Monotone f)
    (R₀ : ℕ) (hpos : ∀ n≥R₀, 0<f n) (C : ℝ) (hC : 0≤C)
    (d b : ℕ) (hb : 2≤b) (hpoly : ∀ R, ∃ n≥R, f n≤C*(n:ℝ)^d) :
    ∀ R : ℕ, ∃ n≥max R R₀, f (b*n)≤(b:ℝ)^(d+1)*f n := by
  intro R
  by_contra! hbad
  let a := max (max R R₀) 1
  have ha : 0<a := by dsimp [a]; omega
  have haR : max R R₀≤a := le_max_left _ _
  have hfapos : 0<f a := hpos a ((le_max_right R R₀).trans haR)
  have hgrow : ∀ k : ℕ, ((b:ℝ)^(d+1))^k*f a≤f (b^k*a) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hr : max R R₀≤b^k*a := haR.trans (by
        have hh : 1≤b^k := Nat.one_le_pow k b (by omega)
        nlinarith)
      have hh := (hbad (b^k*a) hr).le
      calc
        _ = (b:ℝ)^(d+1)*(((b:ℝ)^(d+1))^k*f a) := by rw [pow_succ]; ring
        _ ≤ (b:ℝ)^(d+1)*f (b^k*a) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ f (b*(b^k*a)) := hh
        _ = _ := by congr 1; rw [pow_succ]; ring
  obtain ⟨N,hN⟩ := exists_nat_gt (C*((b*a:ℕ):ℝ)^d/f a)
  have hNF : C*((b*a:ℕ):ℝ)^d<(N:ℝ)*f a := (div_lt_iff₀ hfapos).mp hN
  obtain ⟨n,hn,hnpoly⟩ := hpoly (b*a*(N+1))
  have hnA : b*(N+1)≤n/a := (Nat.le_div_iff_mul_le ha).mpr (by nlinarith)
  have hnAp : n/a≠0 := by nlinarith
  let k := Nat.log b (n/a)
  let P := b^k
  have hP : P≤n/a := Nat.pow_log_le_self b hnAp
  have hP' : n/a<b*P := by
    have hh := Nat.lt_pow_of_log_lt (b := b) (x := k+1) (y := n/a) hb
      (show Nat.log b (n/a)<k+1 by omega)
    simpa only [pow_succ,Nat.mul_comm] using hh
  have hNP : N<P := by nlinarith
  have hNP' : (N:ℝ)<P := by exact_mod_cast hNP
  have hPA : P*a≤n := (Nat.le_div_iff_mul_le ha).mp hP
  have hnupper : n<(b*P)*a := (Nat.div_lt_iff_lt_mul ha).mp hP'
  have hlow : (P:ℝ)^d*((P:ℝ)*f a)≤f n := by
    have hh := (hgrow k).trans (hf hPA)
    have he : (P:ℝ)^d*((P:ℝ)*f a) = ((b:ℝ)^(d+1))^k*f a := by
      dsimp [P]
      push_cast
      rw [←mul_assoc,←pow_succ,←pow_mul,←pow_mul,Nat.mul_comm k (d+1)]
    rw [he]
    exact hh
  have hupper : f n≤(P:ℝ)^d*(C*((b*a:ℕ):ℝ)^d) := by
    have hnupper' : (n:ℝ)≤((b*P)*a:ℕ) := by exact_mod_cast hnupper.le
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hnupper' d) hC
    apply hnpoly.trans
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  have hPpos : (0:ℝ)<(P:ℝ)^d := by
    apply pow_pos
    exact_mod_cast (show 0<P by dsimp [P]; positivity)
  have hsmall : C*((b*a:ℕ):ℝ)^d<(P:ℝ)*f a :=
    hNF.trans (mul_lt_mul_of_pos_right hNP' hfapos)
  exact (not_lt_of_ge (hlow.trans hupper)) (mul_lt_mul_of_pos_left hsmall hPpos)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_PolynomialFolner
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Finset
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis

lemma sparse_small_increment (f : ℕ → ℝ) (hf : Monotone f)
    (hp : ∀ n, 0<f n) (C : ℝ) (hC : 0≤C) (d : ℕ)
    (hg : ∀ R, ∃ n≥R, f n≤C*(n:ℝ)^d)
    (ε : ℝ) (hε : 0<ε) (R : ℕ) :
    ∃ n≥R, f (n+1)-f n≤ε*f n := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((2:ℝ)^(d+1)/ε)
  obtain ⟨r,hr,hgood⟩ := sparse_real_doubling f hf 0 (fun n _ => hp n)
    C hC d 2 (by omega) hg (max R N)
  have hR : R ≤ r := by omega
  have hlarge : (2:ℝ)^(d+1)<(r:ℝ)*ε := by
    have hn : (N:ℝ) ≤ r := by exact_mod_cast (show N ≤ r by omega)
    have he := (div_lt_iff₀ hε).mp hN
    nlinarith
  by_contra! hbad
  have ht : ∀ i ≤ r, (i:ℝ)*ε*f r≤f (r+i)-f r := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have h := ih (by omega)
      have hh := (hbad (r+i) (by omega)).le
      have hm := hf (show r ≤ r+i by omega)
      have him := mul_le_mul_of_nonneg_left hm hε.le
      push_cast
      have he : r+(i+1)=r+i+1 := by omega
      rw [he]
      nlinarith
  have h := ht r le_rfl
  rw [←two_mul] at h
  have hh := mul_lt_mul_of_pos_right hlarge (hp r)
  norm_num only [Nat.cast_ofNat] at hgood
  nlinarith [hp r]

lemma sum_sub_sum_bound_common_superset {A : Type*} (T U V : Finset A)
    (hUT : U⊆T) (hVT : V⊆T) (hcard : U.card=V.card)
    (f : A → ℝ) (M : ℝ) (hM : 0≤M) (hb : ∀ x∈T, |f x|≤M) :
    |(∑ x∈U, f x)-(∑ x∈V, f x)|≤2*((T.card:ℝ)-U.card)*M := by
  have hu : (∑ x∈U, f x)+(∑ x∈T\U, f x)=∑ x∈T, f x :=
    by rw [Finset.sum_sdiff_eq_sub hUT]; ring
  have hv : (∑ x∈V, f x)+(∑ x∈T\V, f x)=∑ x∈T, f x :=
    by rw [Finset.sum_sdiff_eq_sub hVT]; ring
  have hs (W : Finset A) (hWT : W⊆T) : |∑ x∈T\W, f x|≤((T.card:ℝ)-W.card)*M := by
    calc
      _ ≤ ∑ x∈T\W, |f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x∈T\W, M := Finset.sum_le_sum (fun x hx => hb x (Finset.mem_sdiff.mp hx).1)
      _ = _ := by
        rw [Finset.sum_const,Finset.card_sdiff_of_subset hWT,nsmul_eq_mul,Nat.cast_sub (Finset.card_le_card hWT)]
  have he : (∑ x∈U, f x)-(∑ x∈V, f x)=(∑ x∈T\V, f x)-(∑ x∈T\U, f x) := by linarith
  rw [he]
  apply (abs_sub _ _).trans
  calc
    _ ≤ (((T.card:ℝ)-V.card)+((T.card:ℝ)-U.card))*M := by
      linarith [hs V hVT, hs U hUT]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [←hcard]; linarith) hM

end CriticalPercolation.HarmonicAnalysis
namespace CriticalPercolation.SparseGrowth
variable {G : Type*} [Group G] [DecidableEq G]

lemma small_ball_increment (S : Finset G) (h1 : (1:G)∈S) (d : ℕ)
    (hg : HasDegree S d) (ε : ℝ) (hε : 0<ε) (R : ℕ) :
    ∃ n≥R, ((S^(n+1)).card:ℝ)-(S^n).card≤ε*(S^n).card := by
  obtain ⟨C,hC⟩ := hg
  apply HarmonicAnalysis.sparse_small_increment (fun n => ((S^n).card:ℝ))
    (fun i j hij => by dsimp; exact_mod_cast Finset.card_le_card (Finset.pow_subset_pow_right h1 hij))
    (fun n => by exact_mod_cast Finset.card_pos.mpr ⟨1,Finset.one_mem_pow h1⟩)
    C (Nat.cast_nonneg C) d ?_ ε hε R
  intro T
  obtain ⟨n,hn,hb⟩ := hC T
  exact ⟨n,hn,by exact_mod_cast hb⟩

lemma translated_ball_sum_bound (S : Finset G) (h1 : (1:G)∈S)
    (n : ℕ) (s : G) (hs : s∈S) (f : G → ℝ) (M : ℝ)
    (hM : 0≤M) (hb : ∀ x, |f x|≤M) :
    |(∑ x∈S^n, f (s*x))-(∑ x∈S^n, f x)|≤
      2*(((S^(n+1)).card:ℝ)-(S^n).card)*M := by
  have hT : (S^n).image (fun x => s*x)⊆S^(n+1) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [pow_succ']
    exact Finset.mul_mem_mul hs ha
  have hU : S^n⊆S^(n+1) := Finset.pow_subset_pow_right h1 (Nat.le_succ n)
  have he : ((S^n).image (fun x => s*x)).card=(S^n).card :=
    Finset.card_image_of_injective _ (mul_right_injective s)
  have H := HarmonicAnalysis.sum_sub_sum_bound_common_superset
    (S^(n+1)) ((S^n).image (fun x => s*x)) (S^n) hT hU he f M hM (fun x _ => hb x)
  rw [he,Finset.sum_image (fun x _ y _ h => mul_left_cancel h)] at H
  exact H

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FieldSpanTransfer
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical BigOperators

namespace CriticalPercolation.LinearGrowth
variable {K L T i J : Type*} [Field K] [Field L] [Field T] [Fintype i]

lemma pi_span_map_top (f : K →+* T) (v : J → i → K)
    (hv : Submodule.span K (Set.range v)=⊤) :
    Submodule.span T (Set.range (fun j k => f (v j k)))=⊤ := by
  let P := Submodule.span T (Set.range (fun j k => f (v j k)))
  have hm (x : i → K) : (fun k => f (x k))∈P := by
    have hx : x∈Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨j,rfl⟩ := hx; exact Submodule.subset_span ⟨j,rfl⟩
    | zero => simpa only [Pi.zero_def,Pi.zero_apply,map_zero] using P.zero_mem
    | add x y hx hy ihx ihy => simpa only [Pi.add_def,Pi.add_apply,map_add] using P.add_mem ihx ihy
    | smul c x hx ih => simpa only [Pi.smul_def,Pi.smul_apply,smul_eq_mul,map_mul] using P.smul_mem (f c) ih
  apply top_unique
  rw [←(Pi.basisFun T i).span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨k,rfl⟩
  have he : (Pi.basisFun T i) k=(fun l => f ((Pi.single k (1:K) : i → K) l)) := by
    ext l
    simp [Pi.basisFun_apply,Pi.single_apply]
  rw [he]
  exact hm (Pi.single k 1)

lemma pi_span_descends (f : L →+* T) (w : J → i → L)
    (hw : Submodule.span T (Set.range (fun j k => f (w j k)))=⊤) :
    Submodule.span L (Set.range w)=⊤ := by
  by_contra hn
  obtain ⟨φ,hφ,hker⟩ := (Submodule.span L (Set.range w)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hn)
  let c (k : i) := φ (Pi.single k 1)
  have hφsum (x : i → L) : φ x=∑ k, x k*c k := by
    conv_lhs => rw [←(Pi.basisFun L i).sum_repr x]
    simp [c,Pi.basisFun_apply,Pi.basisFun_repr, map_sum,map_smul,smul_eq_mul]
  let ψ : (i → T) →ₗ[T] T := {
    toFun x := ∑ k, x k*f (c k)
    map_add' x y := by simp [add_mul,Finset.sum_add_distrib]
    map_smul' a x := by simp [smul_eq_mul,Finset.mul_sum,mul_assoc] }
  have hker' : Submodule.span T (Set.range (fun j k => f (w j k)))≤ψ.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    change (∑ k, f (w j k)*f (c k))=0
    simp_rw [←map_mul]
    rw [←map_sum,←hφsum]
    have he : φ (w j)=0 := hker (Submodule.subset_span ⟨j,rfl⟩)
    rw [he,map_zero]
  have hψ : ψ=0 := LinearMap.ker_eq_top.mp (top_unique (hw ▸ hker'))
  apply hφ
  apply LinearMap.ext
  intro x
  change φ x=0
  rw [hφsum]
  apply Finset.sum_eq_zero
  intro k hk
  have he := congrArg (fun a : (i → T) →ₗ[T] T => a (Pi.single k 1)) hψ
  have hc : c k=0 := f.injective (by simpa [ψ,Pi.single_apply] using he)
  rw [hc,mul_zero]

lemma pi_span_transfer (f : K →+* T) (e : L →+* T)
    (v : J → i → K) (w : J → i → L)
    (hm : ∀ j k, f (v j k)=e (w j k))
    (hv : Submodule.span K (Set.range v)=⊤) : Submodule.span L (Set.range w)=⊤ := by
  apply pi_span_descends e w
  simpa only [hm] using pi_span_map_top f v hv

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FiniteSubspaceOrbit
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

lemma finiteIndex_subspace_stabilizer (ρ : G →* (V ≃ₗ[K] V))
    (W : Submodule K V)
    (hf : (Set.range (fun g => W.map (ρ g).toLinearMap)).Finite) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∀ h : H, W.map (ρ h).toLinearMap=W := by
  let := subspaceAction ρ
  let H := MulAction.stabilizer G W
  have horb : (MulAction.orbit G W).Finite := hf
  let : Finite (MulAction.orbit G W) := horb.to_subtype
  let : Finite (G ⧸ H) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G W)
  refine ⟨H,Subgroup.finiteIndex_of_finite_quotient,?_⟩
  intro h
  exact h.property

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_CompactInvariantMeasure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Finset MeasureTheory
open scoped Classical Topology BigOperators Pointwise ENNReal NNReal BoundedContinuousFunction

namespace CriticalPercolation.SparseGrowth
variable {G X : Type*} [Group G] [DecidableEq G]
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

omit [DecidableEq G] [ContinuousConstSMul G X] in
lemma integral_orbitAverage (T : Finset G) (hT : T.Nonempty) (x : X)
    (f : X → ℝ) :
    ∫ y, f y ∂(orbitAverage T hT x:Measure X) =
      (T.card:ℝ)⁻¹ * ∑ g∈T, f (g • x) := by
  change ∫ y, f y ∂(((T.card:ℝ≥0∞)⁻¹) • ∑ g∈T, Measure.dirac (g • x))=_
  rw [integral_smul_measure,integral_finsetSum_measure (fun g _ => integrable_dirac (by finiteness))]
  simp only [integral_dirac,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]

omit [ContinuousConstSMul G X] in
lemma orbitAverage_translate_bound (S : Finset G) (h1 : (1:G)∈S)
    (n : ℕ) (x : X) (s : G) (hs : s∈S) (f : X →ᵇ ℝ) :
    |(∫ y, f (s • y) ∂(orbitAverage (S^n) (orbit_wordBall_nonempty S h1 n) x:Measure X))-
      (∫ y, f y ∂(orbitAverage (S^n) (orbit_wordBall_nonempty S h1 n) x:Measure X))| ≤
      ((S^n).card:ℝ)⁻¹ * (2*(((S^(n+1)).card:ℝ)-(S^n).card)*‖f‖) := by
  rw [integral_orbitAverage (S^n) _ x (fun y => f (s • y)),
    integral_orbitAverage (S^n) _ x f,←mul_sub,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  simpa only [mul_smul] using translated_ball_sum_bound S h1 n s hs
    (fun g => f (g • x)) ‖f‖ (norm_nonneg _) (fun g => by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (g • x))

lemma exists_invariant_probability_measure_generators [CompactSpace X]
    (S : Finset G) (h1 : (1:G)∈S) (d : ℕ) (hg : HasDegree S d) (x : X) :
    ∃ μ : ProbabilityMeasure X, ∀ s∈S, ∀ f : X →ᵇ ℝ,
      (∫ y, f (s • y) ∂(μ:Measure X))=∫ y, f y ∂(μ:Measure X) := by
  have hex : ∀ k : ℕ, ∃ n≥k,
      ((S^(n+1)).card:ℝ)-(S^n).card≤((k:ℝ)+1)⁻¹*(S^n).card := by
    intro k
    exact small_ball_increment S h1 d hg _ (by positivity) k
  choose r hr hsmall using hex
  let ν : ℕ → ProbabilityMeasure X := fun k => orbitAverage (S^(r k)) (orbit_wordBall_nonempty S h1 (r k)) x
  obtain ⟨μ,_,φ,hφ,hlim⟩ := (isCompact_univ : IsCompact (Set.univ:Set (ProbabilityMeasure X))).tendsto_subseq
    (x:=ν) (fun _ => Set.mem_univ _)
  refine ⟨μ,?_⟩
  intro s hs f
  let fs : X →ᵇ ℝ := f.compContinuous ⟨fun y => s • y,continuous_const_smul s⟩
  have he0 : Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun k => 2*‖f‖*((φ k:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa using (he0.comp hφ.tendsto_atTop).const_mul (2*‖f‖)
  have hb (k : ℕ) :
      |(∫ y, fs y ∂(ν (φ k):Measure X))-(∫ y, f y ∂(ν (φ k):Measure X))|≤
        2*‖f‖*((φ k:ℝ)+1)⁻¹ := by
    apply (orbitAverage_translate_bound S h1 (r (φ k)) x s hs f).trans
    have hc : (0:ℝ)<(S^(r (φ k))).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1,Finset.one_mem_pow h1⟩
    have hm := mul_le_mul_of_nonneg_left (hsmall (φ k))
      (show 0≤((S^(r (φ k))).card:ℝ)⁻¹ * (2*‖f‖) by positivity)
    calc
      _ = ((S^(r (φ k))).card:ℝ)⁻¹ * (2*‖f‖) *
          (((S^(r (φ k)+1)).card:ℝ)-(S^(r (φ k))).card) := by ring
      _ ≤ ((S^(r (φ k))).card:ℝ)⁻¹ * (2*‖f‖) *
          (((φ k:ℝ)+1)⁻¹*(S^(r (φ k))).card) := hm
      _ = _ := by field_simp
  have hz : Tendsto (fun k => (∫ y, fs y ∂(ν (φ k):Measure X))-
      (∫ y, f y ∂(ν (φ k):Measure X))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by simpa only [Real.norm_eq_abs] using hb k) he
  have hfs := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction fs).tendsto μ |>.comp hlim
  have hf := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).tendsto μ |>.comp hlim
  exact sub_eq_zero.mp (tendsto_nhds_unique (hfs.sub hf) hz)

end CriticalPercolation.SparseGrowth

namespace CriticalPercolation.SparseGrowth
variable {G X : Type*} [Group G] [DecidableEq G]
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

lemma exists_invariant_probability_measure [CompactSpace X]
    (S : Finset G) (h1 : (1:G)∈S) (hgen : Subgroup.closure (S:Set G)=⊤)
    (d : ℕ) (hg : HasDegree S d) (x : X) :
    ∃ μ : ProbabilityMeasure X, ∀ g : G,
      Measure.map (fun y => g • y) (μ:Measure X)=(μ:Measure X) := by
  obtain ⟨μ,hμ⟩ := exists_invariant_probability_measure_generators S h1 d hg x
  have hle : Subgroup.closure (S:Set G) ≤ integralInvariantSubgroup μ :=
    (Subgroup.closure_le _).mpr (fun s hs => hμ s hs)
  rw [hgen] at hle
  refine ⟨μ,?_⟩
  intro g
  have hi : ∀ f : X →ᵇ ℝ, (∫ y, f (g • y) ∂(μ:Measure X))=∫ y, f y ∂(μ:Measure X) :=
    hle (Subgroup.mem_top g)
  let ν : ProbabilityMeasure X := μ.map (f := (fun point => g • point)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have he : ν.toFiniteMeasure=μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    change (∫ y, f y ∂(Measure.map (fun y => g • y) (μ:Measure X)))=_
    rw [integral_map (continuous_const_smul g).measurable.aemeasurable f.continuous.aestronglyMeasurable]
    exact hi f
  exact congrArg FiniteMeasure.toMeasure he

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_LocalProjectiveAction
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory Module Metric TopologicalSpace
open scoped Classical Topology

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

lemma continuous_action (a : V ≃L[K] V) : Continuous (action a) := by
  apply (openQuotient_point K V).isQuotientMap.continuous_iff.mpr
  exact (continuous_point K V).comp ((a.continuous.comp continuous_subtype_val).subtype_mk _)

variable {G : Type*} [Group G]

lemma continuousConstSMul (ρ : G →* (V ≃L[K] V)) :
    letI := mulAction ρ; ContinuousConstSMul G (Space K V) := by
  let := mulAction ρ
  exact ⟨fun g => continuous_action (ρ g)⟩

lemma exists_invariant_measure [ProperSpace K] [FiniteDimensional K V] [Nontrivial V]
    [DecidableEq G] (ρ : G →* (V ≃L[K] V)) (S : Finset G)
    (h1 : (1:G)∈S) (hgen : Subgroup.closure (S:Set G)=⊤)
    (d : ℕ) (hg : SparseGrowth.HasDegree S d) :
    ∃ μ : Measure (Space K V), IsProbabilityMeasure μ ∧
      ∀ g, Measure.map (action (ρ g)) μ=μ := by
  let : MetricSpace (Space K V) := metrizableSpaceMetric _
  let := mulAction ρ
  let := continuousConstSMul ρ
  obtain ⟨v,hv⟩ := exists_ne (0:V)
  obtain ⟨μ,hμ⟩ := SparseGrowth.exists_invariant_probability_measure S h1 hgen d hg (point K V ⟨v,hv⟩)
  exact ⟨μ,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),hμ⟩

lemma point_mem_subspace (W : Submodule K V) (v : NZ V) :
    point K V v∈subspace W ↔ (v:V)∈W := by
  constructor
  · rintro ⟨w,hw,he⟩
    obtain ⟨a,ha⟩ := (point_eq_iff v w).mp he.symm
    exact ha ▸ W.smul_mem a hw
  · intro hv
    exact ⟨v,hv,rfl⟩

lemma preimage_point_subspace (W : Submodule K V) :
    point K V ⁻¹' subspace W={v : NZ V | (v:V)∈W} := by
  ext v
  exact point_mem_subspace W v

lemma closed_subspace [CompleteSpace K] [FiniteDimensional K V] (W : Submodule K V) :
    IsClosed (subspace W) := by
  apply (openQuotient_point K V).isQuotientMap.isClosed_preimage.mp
  rw [preimage_point_subspace]
  exact W.closed_of_finiteDimensional.preimage continuous_subtype_val

lemma measurable_subspace [CompleteSpace K] [FiniteDimensional K V] (W : Submodule K V) :
    MeasurableSet (subspace W) := (closed_subspace W).measurableSet

@[simp] lemma subspace_inf (U W : Submodule K V) :
    subspace (U⊓W)=subspace U∩subspace W := by
  ext q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  simp only [mem_inter_iff,point_mem_subspace,Submodule.mem_inf]

@[simp] lemma subspace_bot : subspace (⊥:Submodule K V)=∅ := by
  ext q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  simp only [point_mem_subspace,Submodule.mem_bot,mem_empty_iff_false,iff_false]
  exact v.property

@[simp] lemma subspace_top : subspace (⊤:Submodule K V)=univ := by
  ext q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  simp only [point_mem_subspace,Submodule.mem_top,mem_univ]

lemma preimage_action_subspace (a : V ≃L[K] V) (W : Submodule K V) :
    action a ⁻¹' subspace (W.map a.toLinearEquiv.toLinearMap)=subspace W := by
  ext q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  simp only [mem_preimage,action_point,point_mem_subspace]
  change a (v:V)∈W.map a.toLinearEquiv.toLinearMap ↔ (v:V)∈W
  constructor
  · rintro ⟨w,hw,he⟩
    exact a.injective he ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_LocalFurstenbergConcentration
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory NormedSpace Module Metric TopologicalSpace
open scoped Classical Topology ENNReal

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
variable [ProperSpace K] [FiniteDimensional K V]

lemma subspace_full_of_singular_limit
    (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (a : ℕ → V ≃L[K] V) (c : ℕ → K) (hc : ∀ n, c n≠0)
    (A : V →L[K] V) (hA : A≠0)
    (hlim : Tendsto (fun n => c n • (a n).toContinuousLinearMap) atTop (𝓝 A))
    (hμ : ∀ n, Measure.map (action (a n)) μ=μ)
    (hker : μ (subspace A.toLinearMap.ker)=0) :
    ∀ᵐ q ∂μ, q∈subspace A.toLinearMap.range := by
  let : MetricSpace (Space K V) := metrizableSpaceMetric _
  let L : Set (Space K V) := subspace A.toLinearMap.range
  have hL : IsClosed L := closed_subspace _
  have hLne : L.Nonempty := by
    have hex : ∃ x : V, A x≠0 := by
      by_contra hn
      push Not at hn
      exact hA (ContinuousLinearMap.ext hn)
    obtain ⟨x,hx⟩ := hex
    exact ⟨point K V ⟨A x,hx⟩,(point_mem_subspace _ _).mpr ⟨x,rfl⟩⟩
  let f : Space K V → ℝ := fun q => min 1 (infDist q L)
  have hfcont : Continuous f := continuous_const.min (continuous_infDist_pt L)
  have hfnonneg (q : Space K V) : 0≤f q := le_min zero_le_one infDist_nonneg
  have hfbound (q : Space K V) : ‖f q‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hfnonneg q)]
    exact min_le_left _ _
  have hfi : Integrable f μ := (integrable_const (1:ℝ)).mono' hfcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hfbound)
  have hx : ∀ᵐ q ∂μ, q∉subspace A.toLinearMap.ker := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hker
  have hpoint : ∀ᵐ q ∂μ, Tendsto (fun n => f (action (a n) q)) atTop (𝓝 0) := by
    filter_upwards [hx] with q hq
    obtain ⟨v,rfl⟩ := point_surjective K V q
    have hv : A (v:V)≠0 := by
      simpa only [point_mem_subspace,LinearMap.mem_ker,ContinuousLinearMap.coe_coe] using hq
    let w : ℕ → NZ V := fun n => ⟨(c n • (a n).toContinuousLinearMap) (v:V),
      smul_ne_zero (hc n) (nzImage (a n) v).property⟩
    have hev : Tendsto (fun n => (c n • (a n).toContinuousLinearMap) (v:V)) atTop (𝓝 (A v)) :=
      ((continuous_id.clm_apply continuous_const).tendsto A).comp hlim
    have hw : Tendsto w atTop (𝓝 ⟨A v,hv⟩) := tendsto_subtype_rng.mpr hev
    have hp := (continuous_point K V).continuousAt.tendsto.comp hw
    have he (n : ℕ) : point K V (w n)=action (a n) (point K V v) := by
      rw [action_point,point_eq_iff]
      exact ⟨c n,rfl⟩
    change Tendsto (fun n => point K V (w n)) atTop (𝓝 (point K V ⟨A v,hv⟩)) at hp
    simp_rw [he] at hp
    have hf := hfcont.continuousAt.tendsto.comp hp
    have hin : point K V ⟨A v,hv⟩∈L := (point_mem_subspace _ _).mpr ⟨v,rfl⟩
    have hz : f (point K V ⟨A v,hv⟩)=0 := by
      simp only [f,infDist_zero_of_mem hin,min_eq_right zero_le_one]
    rw [hz] at hf
    exact hf
  have hconv := tendsto_integral_of_dominated_convergence (μ:=μ)
    (F:=fun n q => f (action (a n) q)) (f:=fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (fun n => (hfcont.comp (continuous_action (a n))).aestronglyMeasurable)
    (integrable_const 1) (fun n => Filter.Eventually.of_forall (fun q => hfbound _)) hpoint
  have he (n : ℕ) : (∫ q, f (action (a n) q) ∂μ)=∫ q, f q ∂μ := by
    rw [←integral_map (continuous_action (a n)).measurable.aemeasurable hfcont.aestronglyMeasurable,
      hμ n]
  simp_rw [he] at hconv
  have hint : (∫ q, f q ∂μ)=0 := by
    exact tendsto_nhds_unique tendsto_const_nhds (by simpa only [integral_zero] using hconv)
  have hz := (integral_eq_zero_iff_of_nonneg hfnonneg hfi).mp hint
  filter_upwards [hz] with q hq
  apply (hL.mem_iff_infDist_zero hLne).mpr
  change min 1 (infDist q L)=0 at hq
  rcases min_choice (1:ℝ) (infDist q L) with he|he
  · rw [he] at hq
    norm_num at hq
  · exact he.symm.trans hq

lemma injective_of_nonzero_projective_limit
    (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (hn : ∀ W : Submodule K V, W≠⊤ → μ (subspace W)=0)
    (a : ℕ → V ≃L[K] V) (c : ℕ → K) (hc : ∀ n, c n≠0)
    (A : V →L[K] V) (hA : A≠0)
    (hlim : Tendsto (fun n => c n • (a n).toContinuousLinearMap) atTop (𝓝 A))
    (hμ : ∀ n, Measure.map (action (a n)) μ=μ) : Injective A := by
  have hk : A.toLinearMap.ker≠⊤ := by
    intro he
    apply hA
    ext x
    have hx : x∈A.toLinearMap.ker := he ▸ Submodule.mem_top
    exact hx
  have hae := subspace_full_of_singular_limit μ a c hc A hA hlim hμ (hn _ hk)
  have hr : A.toLinearMap.range=⊤ := by
    by_contra hr
    have hnot : ∀ᵐ q ∂μ, q∉subspace A.toLinearMap.range := by
      rw [ae_iff]
      simpa only [not_not,Set.ofPred_mem_eq] using hn _ hr
    obtain ⟨q,hq,hq'⟩ := (hae.and hnot).exists
    exact hq' hq
  exact LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp hr)

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_LocalPositiveSubspaceOrbit
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory NormedSpace Module
open scoped Classical Topology ENNReal

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
variable [CompleteSpace K] [FiniteDimensional K V]

omit [CompleteSpace K] in
lemma small_intersection_rank (U W : Submodule K V)
    (he : finrank K U=finrank K W) (hne : U≠W) :
    finrank K ↥(U⊓W)<finrank K U := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left ?_
  intro hi
  have hle : U≤W := by rw [←hi]; exact inf_le_right
  exact hne (Submodule.eq_of_le_of_finrank_eq hle he)

lemma finite_positive_subspaces (μ : Measure (Space K V)) [IsFiniteMeasure μ]
    (d : ℕ) (ε : ℝ≥0∞) (hε : ε≠0)
    (hnull : ∀ W : Submodule K V, finrank K W<d → μ (subspace W)=0) :
    {W : Submodule K V | finrank K W=d ∧ ε≤μ (subspace W)}.Finite := by
  let T := {W : Submodule K V | finrank K W=d ∧ ε≤μ (subspace W)}
  by_contra hfin
  have hinf : T.Infinite := hfin
  let : Infinite T := hinf.to_subtype
  have hdis : Pairwise (AEDisjoint μ on (fun W:T => subspace W.val)) := by
    intro U W hne
    change μ (subspace U.val∩subspace W.val)=0
    rw [←subspace_inf]
    apply hnull
    rw [←U.property.1]
    apply small_intersection_rank _ _ (U.property.1.trans W.property.1.symm)
    exact fun he => hne (Subtype.ext he)
  have hs := tsum_measure_le_measure_univ
    (fun W:T => (measurable_subspace W.val).nullMeasurableSet) hdis
  have hc : (∑' _ : T, ε)≤∑' W:T, μ (subspace W.val) :=
    ENNReal.tsum_le_tsum (fun W => W.property.2)
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hε] at hc
  exact (measure_ne_top μ Set.univ) (top_unique (hc.trans hs))

omit [CompleteSpace K] in
lemma exists_minimal_positive_subspace (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (h : ∃ W : Submodule K V, W≠⊤ ∧ μ (subspace W)≠0) :
    ∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧ μ (subspace W)≠0 ∧
      ∀ U : Submodule K V, finrank K U<finrank K W → μ (subspace U)=0 := by
  have hex : ∃ d:ℕ, ∃ W : Submodule K V,
      finrank K W=d ∧ W≠⊤ ∧ μ (subspace W)≠0 := by
    obtain ⟨W,hW,hμ⟩ := h
    exact ⟨finrank K W,W,rfl,hW,hμ⟩
  obtain ⟨W,hWd,hWt,hWμ⟩ := Nat.find_spec hex
  refine ⟨W,?_,hWt,hWμ,?_⟩
  · intro he
    exact hWμ (by simp [he])
  · intro U hU
    by_contra hUμ
    have hut : U≠⊤ := by
      intro he
      have hh := Submodule.finrank_le W
      rw [he,finrank_top] at hU
      omega
    have hi := Nat.find_min' hex ⟨U,rfl,hut,hUμ⟩
    omega

lemma measure_subspace_map_eq (μ : Measure (Space K V))
    (a : V ≃L[K] V) (hμ : Measure.map (action a) μ=μ)
    (W : Submodule K V) :
    μ (subspace (W.map a.toLinearEquiv.toLinearMap))=μ (subspace W) := by
  conv_lhs => rw [←hμ]
  rw [Measure.map_apply (continuous_action a).measurable
    (measurable_subspace _),preimage_action_subspace]

lemma exists_finite_positive_subspace_orbit {G : Type*} [Group G]
    (ρ : G →* (V ≃L[K] V)) (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (hμ : ∀ g, Measure.map (action (ρ g)) μ=μ)
    (h : ∃ W : Submodule K V, W≠⊤ ∧ μ (subspace W)≠0) :
    ∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧
      (Set.range (fun g => W.map (ρ g).toLinearEquiv.toLinearMap)).Finite := by
  obtain ⟨W,hWb,hWt,hWμ,hnull⟩ := exists_minimal_positive_subspace μ h
  refine ⟨W,hWb,hWt,?_⟩
  apply (finite_positive_subspaces μ (finrank K W) _ hWμ hnull).subset
  rintro U ⟨g,rfl⟩
  refine ⟨(ρ g).toLinearEquiv.finrank_map_eq W,?_⟩
  exact (measure_subspace_map_eq μ (ρ g) (hμ g) W).ge

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_LocalFurstenbergBound
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory NormedSpace Module Metric TopologicalSpace
open scoped Classical Topology ENNReal

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

variable (t : K) (ht : 1<‖t‖)
include ht
lemma shellScalar_spec {U : Type*} [NormedAddCommGroup U] [NormedSpace K U]
    (x : U) (hx : x≠0) : shellScalar t ht x hx≠0 ∧
      1/‖t‖≤‖shellScalar t ht x hx • x‖ ∧ ‖shellScalar t ht x hx • x‖≤1 :=
  Classical.choose_spec (exists_shell_scalar t ht x hx)

variable [Nontrivial V]

omit ht in
lemma compact_shell {U : Type*} [NormedAddCommGroup U] [ProperSpace U] : IsCompact (shell t U) := by
  have he : shell t U=closedBall (0:U) 1 ∩ {x | 1/‖t‖≤‖x‖} := by
    ext x
    simp only [shell,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right,and_comm]
  rw [he]
  exact (isCompact_closedBall (0:U) 1).inter_right (isClosed_le continuous_const continuous_norm)

lemma normalized_mem (a : V ≃L[K] V) : normalized t ht a∈shell t (V →L[K] V) :=
  (shellScalar_spec t ht _ (equiv_operator_ne_zero a)).2

variable [ProperSpace K] [FiniteDimensional K V]
variable {G : Type*} [Group G]
lemma normalizedClosure_compact (ρ : G →* (V ≃L[K] V)) :
    IsCompact (closure (Set.range (fun g => normalized t ht (ρ g)))) := by
  let : ProperSpace (V →L[K] V) := FiniteDimensional.proper K _
  apply (compact_shell t).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (compact_shell t).isClosed
  rintro A ⟨g,rfl⟩
  exact normalized_mem t ht _

lemma normalizedClosure_injective (ρ : G →* (V ≃L[K] V))
    (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (hn : ∀ W : Submodule K V, W≠⊤ → μ (subspace W)=0)
    (hμ : ∀ g, Measure.map (action (ρ g)) μ=μ)
    (A : V →L[K] V) (hA : A∈closure (Set.range (fun g => normalized t ht (ρ g)))) :
    Injective A := by
  let : ProperSpace (V →L[K] V) := FiniteDimensional.proper K _
  obtain ⟨B,hB,hlim⟩ := mem_closure_iff_seq_limit.mp hA
  choose g hg using hB
  have hnorm : A∈shell t (V →L[K] V) := by
    apply closure_minimal _ (compact_shell t).isClosed hA
    rintro B ⟨g,rfl⟩
    exact normalized_mem t ht _
  have hne : A≠0 := by
    intro he
    have hp : 0<1/‖t‖ := div_pos zero_lt_one (lt_trans zero_lt_one ht)
    have hh := hnorm.1
    rw [he,norm_zero] at hh
    exact hp.not_ge hh
  apply injective_of_nonzero_projective_limit μ hn (fun n => ρ (g n))
    (fun n => shellScalar t ht _ (equiv_operator_ne_zero (ρ (g n))))
    (fun n => (shellScalar_spec t ht _ (equiv_operator_ne_zero _)).1) A hne _ (fun n => hμ _)
  change Tendsto (fun n => normalized t ht (ρ (g n))) atTop (𝓝 A)
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact hg n

lemma projective_lower_bound_of_null_subspaces
    (ρ : G →* (V ≃L[K] V)) (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (hn : ∀ W : Submodule K V, W≠⊤ → μ (subspace W)=0)
    (hμ : ∀ g, Measure.map (action (ρ g)) μ=μ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ g : G, ∀ x : V,
      δ*‖(ρ g).toContinuousLinearMap‖*‖x‖≤‖ρ g x‖ := by
  let : ProperSpace V := FiniteDimensional.proper K V
  let : ProperSpace (V →L[K] V) := FiniteDimensional.proper K _
  let C := closure (Set.range (fun g => normalized t ht (ρ g)))
  have hC : IsCompact C := normalizedClosure_compact t ht ρ
  obtain ⟨v,hv⟩ := exists_ne (0:V)
  have hne : (C×ˢshell t V).Nonempty :=
    ⟨(normalized t ht (ρ 1),shellScalar t ht v hv • v),subset_closure ⟨1,rfl⟩,
      (shellScalar_spec t ht v hv).2⟩
  have hcont : Continuous (fun z : (V →L[K] V)×V => ‖z.1 z.2‖) :=
    (continuous_fst.clm_apply continuous_snd).norm
  obtain ⟨z,hz,hmin⟩ := (hC.prod (compact_shell t)).exists_isMinOn hne hcont.continuousOn
  have hzinj : Injective z.1 := normalizedClosure_injective t ht ρ μ hn hμ z.1 hz.1
  have hz2 : z.2≠0 := by
    intro he
    have hh := hz.2.1
    rw [he,norm_zero] at hh
    exact (div_pos zero_lt_one (lt_trans zero_lt_one ht)).not_ge hh
  have hδ : 0<‖z.1 z.2‖ := norm_pos_iff.mpr
    (fun he => hz2 (hzinj (he.trans z.1.map_zero.symm)))
  refine ⟨‖z.1 z.2‖,hδ,?_⟩
  intro g x
  by_cases hx : x=0
  · simp [hx]
  let b := shellScalar t ht _ (equiv_operator_ne_zero (ρ g))
  let c := shellScalar t ht x hx
  have hb := (shellScalar_spec t ht _ (equiv_operator_ne_zero (ρ g))).2.2
  have hc := (shellScalar_spec t ht x hx).2.2
  have hsmall := hmin (a := (normalized t ht (ρ g), c • x))
    ⟨subset_closure ⟨g,rfl⟩,(shellScalar_spec t ht x hx).2⟩
  change ‖z.1 z.2‖≤‖(b • (ρ g).toContinuousLinearMap) (c • x)‖ at hsmall
  simp only [smul_apply,map_smul,norm_smul] at hsmall
  change ‖b • (ρ g).toContinuousLinearMap‖≤1 at hb
  change ‖c • x‖≤1 at hc
  rw [norm_smul] at hb hc
  have hp := mul_le_mul hb hc (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
  have hh := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (norm_nonneg (ρ g).toContinuousLinearMap) (norm_nonneg x))
  calc
    _ = ‖z.1 z.2‖ * (‖(ρ g).toContinuousLinearMap‖*‖x‖) := by ring
    _ ≤ _ := hh
    _ = (‖b‖*‖(ρ g).toContinuousLinearMap‖*(‖c‖*‖x‖))*‖ρ g x‖ := by
      change ‖c‖ * (‖b‖ * ‖ρ g x‖) * (‖(ρ g).toContinuousLinearMap‖*‖x‖) = _
      ring
    _ ≤ 1*‖ρ g x‖ := mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hp) (norm_nonneg _)
    _ = _ := one_mul _

omit ht in
lemma sparse_local_furstenberg_alternative [DecidableEq G]
    (ρ : G →* (V ≃L[K] V)) (S : Finset G)
    (h1 : (1:G)∈S) (hgen : Subgroup.closure (S:Set G)=⊤)
    (d : ℕ) (hg : SparseGrowth.HasDegree S d) :
    (∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧
      (Set.range (fun g => W.map (ρ g).toLinearEquiv.toLinearMap)).Finite) ∨
    (∃ δ : ℝ, 0<δ ∧ ∀ g : G, ∀ x : V,
      δ*‖(ρ g).toContinuousLinearMap‖*‖x‖≤‖ρ g x‖) := by
  obtain ⟨t,ht⟩ := NormedField.exists_one_lt_norm K
  obtain ⟨μ,hprob,hμ⟩ := exists_invariant_measure ρ S h1 hgen d hg
  let : IsProbabilityMeasure μ := hprob
  by_cases hn : ∀ W : Submodule K V, W≠⊤ → μ (subspace W)=0
  · exact Or.inr (projective_lower_bound_of_null_subspaces t ht ρ μ hn hμ)
  · push Not at hn
    exact Or.inl (exists_finite_positive_subspace_orbit ρ μ hμ hn)

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FullSpanAlternative
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

lemma submodule_eq_bot_or_top_of_fullSpan (ρ : G →* (V ≃ₗ[K] V)) (hfull : FullSpan ρ)
    (W : Submodule K V) (hinv : ∀ g, W.map (ρ g).toLinearMap=W) : W=⊥ ∨ W=⊤ := by
  by_cases hW : W=⊥
  · exact Or.inl hW
  right
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨φ,hφ⟩ := Projective.exists_dual_eq_one K hw0
  apply top_unique
  intro y _
  let T := φ.smulRight y
  have hT : T∈Submodule.span K (Set.range (fun g => (ρ g).toLinearMap)) := hfull ▸ Submodule.mem_top
  have hm : ∀ A∈Submodule.span K (Set.range (fun g => (ρ g).toLinearMap)), A w∈W := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨g,rfl⟩ := hA
      rw [←hinv g]
      exact Submodule.mem_map.mpr ⟨w,hw,rfl⟩
    | zero => exact W.zero_mem
    | add A B hA hB ihA ihB => exact W.add_mem ihA ihB
    | smul c A hA ihA => exact W.smul_mem c ihA
  simpa only [T,LinearMap.smulRight_apply,hφ,one_smul] using hm T hT

lemma no_finite_subspace_orbit_of_strongFullSpan (ρ : G →* (V ≃ₗ[K] V))
    (hρ : StrongFullSpan ρ) (W : Submodule K V) (hW0 : W≠⊥) (hW1 : W≠⊤) :
    ¬(Set.range (fun g => W.map (ρ g).toLinearMap)).Finite := by
  intro hf
  obtain ⟨H,hHi,hH⟩ := finiteIndex_subspace_stabilizer ρ W hf
  exact (submodule_eq_bot_or_top_of_fullSpan (ρ.comp H.subtype) (hρ H hHi) W hH).elim hW0 hW1

end CriticalPercolation.LinearGrowth
namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V]
variable [NormedSpace K V] [ProperSpace K] [FiniteDimensional K V] [Group G]

lemma projective_bound_of_strongFullSpan [Nontrivial V] [DecidableEq G]
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : StrongFullSpan ρ)
    (S : Finset G) (h1 : (1:G)∈S) (hgen : Subgroup.closure (S:Set G)=⊤)
    (d : ℕ) (hg : SparseGrowth.HasDegree S d) :
    ∃ δ : ℝ, 0<δ ∧ ∀ g : G, ∀ x : V,
      δ*‖(continuousRepresentation ρ g).toContinuousLinearMap‖*‖x‖≤‖ρ g x‖ := by
  rcases LocalProjective.sparse_local_furstenberg_alternative (continuousRepresentation ρ)
    S h1 hgen d hg with horb | hb
  · obtain ⟨W,hW0,hW1,hW⟩ := horb
    exact False.elim (no_finite_subspace_orbit_of_strongFullSpan ρ hρ W hW0 hW1 hW)
  · exact hb

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_AbsoluteMatrixSpan
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K L T G n : Type*} [Field K] [Field L] [Field T] [Group G]
variable [Fintype n] [DecidableEq n]

lemma span_equiv_top {K V W J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (v : J → V)
    (hv : Submodule.span K (Set.range v)=⊤) :
    Submodule.span K (Set.range (fun j => e (v j)))=⊤ := by
  rw [show Set.range (fun j => e (v j))=e '' Set.range v from (Set.range_comp _ _)]
  change Submodule.span K (e.toLinearMap '' Set.range v)=⊤
  rw [←Submodule.map_span e.toLinearMap,hv,Submodule.map_top]
  exact e.range

lemma FullMatrixSpan.fullSpan (ρ : G →* GL n K) (hρ : FullMatrixSpan ρ) :
    FullSpan (matrixRepresentation ρ) := by
  let e := (matrixFlatten (K:=K) (n:=n)).symm.trans Matrix.toLin'
  exact span_equiv_top e (fun g (p:n×n) => ρ g p.1 p.2) hρ

lemma StrongFullMatrixSpan.strongFullSpan (ρ : G →* GL n K) (hρ : StrongFullMatrixSpan ρ) :
    StrongFullSpan (matrixRepresentation ρ) := by
  intro H hH
  exact FullMatrixSpan.fullSpan (ρ.comp H.subtype) (hρ H hH)

lemma FullMatrixSpan.transfer (f : K →+* T) (e : L →+* T)
    (ρ : G →* GL n K) (τ : G →* GL n L)
    (hm : ∀ g i j, f (ρ g i j)=e (τ g i j)) (hρ : FullMatrixSpan ρ) : FullMatrixSpan τ :=
  pi_span_transfer f e (fun g (p:n×n) => ρ g p.1 p.2)
    (fun g (p:n×n) => τ g p.1 p.2) (fun g p => hm g p.1 p.2) hρ

lemma StrongFullMatrixSpan.transfer (f : K →+* T) (e : L →+* T)
    (ρ : G →* GL n K) (τ : G →* GL n L)
    (hm : ∀ g i j, f (ρ g i j)=e (τ g i j)) (hρ : StrongFullMatrixSpan ρ) :
    StrongFullMatrixSpan τ := by
  intro H hH
  exact FullMatrixSpan.transfer f e (ρ.comp H.subtype) (τ.comp H.subtype)
    (fun g i j => hm g i j) (hρ H hH)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_CountableFieldEmbedding
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Cardinal
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma exists_algHom_of_countable {k K F : Type} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [Countable k] [Countable K] [IsAlgClosed F] [Uncountable F] :
    Nonempty (K →ₐ[k] F) := by
  obtain ⟨S,hS⟩ := exists_isTranscendenceBasis k K
  obtain ⟨T,hT⟩ := exists_isTranscendenceBasis k F
  have hcard : #F=#T := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
    _ hT mk_le_aleph0 aleph0_lt_mk
  have hle : #S≤#T := by
    rw [←hcard]
    exact mk_le_aleph0.trans aleph0_lt_mk.le
  obtain ⟨e⟩ := (Cardinal.le_def S T).mp hle
  let y : S → F := fun s => (e s: F)
  have hy : AlgebraicIndependent k y := hT.1.comp e e.injective
  let A := IntermediateField.adjoin k (Set.range (Subtype.val : S → K))
  let φ : A →ₐ[k] F := (IsFractionRing.liftAlgHom
    (algebraicIndependent_iff_injective_aeval.mp hy)).comp hS.1.reprField
  let : Algebra A F := φ.toRingHom.toAlgebra
  let : IsScalarTower k A F := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  let : Algebra.IsAlgebraic A K := hS.isAlgebraic_field
  exact ⟨(IsAlgClosed.lift (R:=A) (S:=K) (M:=F)).restrictScalars k⟩

lemma exists_extension_of_countable {k K F : Type} [Field k] [Field K] [Field F]
    [Algebra k K] [Countable k] [Countable K] [IsAlgClosed F] [Uncountable F]
    (f : k →+* F) : ∃ g : K →+* F, g.comp (algebraMap k K)=f := by
  let : Algebra k F := f.toAlgebra
  obtain ⟨g⟩ := exists_algHom_of_countable (k:=k) (K:=K) (F:=F)
  exact ⟨g.toRingHom,g.comp_algebraMap⟩

lemma uncountable_complete_normed_field (F : Type*) [NontriviallyNormedField F] [CompleteSpace F] :
    Uncountable F := by
  obtain ⟨f,_,_,hf⟩ := (PerfectSpace.univ_perfect (α:=F)).exists_nat_bool_injection Set.univ_nonempty
  let : Uncountable (ℕ → Bool) := Cardinal.aleph0_lt_mk_iff.mp (by
    simpa only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.two_power_aleph0]
      using Cardinal.aleph0_lt_continuum)
  exact hf.uncountable

end CriticalPercolation.Arithmetic
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ArchimedeanDetection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Cardinal
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma exists_transcendental_complex_norm_gt_one : ∃ z : ℂ, Transcendental ℚ z ∧ 1<‖z‖ := by
  have hex : ∃ y : ℝ, Transcendental ℚ y := by
    by_contra hn
    push Not at hn
    let : Algebra.IsAlgebraic ℚ ℝ := ⟨fun x => Classical.not_not.mp (hn x)⟩
    have hh := Algebra.IsAlgebraic.cardinalMk_le_max ℚ ℝ
    have hq : #(ℚ)≤ℵ₀ := mk_le_aleph0
    rw [max_eq_right hq] at hh
    exact (aleph0_lt_mk (α:=ℝ)).not_ge hh
  obtain ⟨y,hy⟩ := hex
  obtain ⟨n,hn⟩ := exists_nat_gt (‖y‖+2)
  have hpos : 1<y+(n:ℝ) := by
    have hab : -‖y‖≤y := by simpa only [Real.norm_eq_abs] using neg_abs_le y
    linarith
  have ht : Transcendental ℚ (y+(n:ℝ)) := by
    intro halg
    exact hy (by simpa only [add_sub_cancel_right] using halg.sub (isAlgebraic_natCast (R:=ℚ) n))
  refine ⟨(y+(n:ℝ):ℝ),?_,?_⟩
  · exact (transcendental_algebraMap_iff (R:=ℚ) (S:=ℝ) (A:=ℂ) (algebraMap ℝ ℂ).injective).mpr ht
  · simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one hpos)] using hpos

lemma exists_embedding_sending_transcendental {k K F : Type} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [Countable k] [Countable K] [IsAlgClosed F] [Uncountable F]
    (x : K) (hx : Transcendental k x) (y : F) (hy : Transcendental k y) :
    ∃ f : K →+* F, f x=y := by
  let v : Unit → K := fun _ => x
  let w : Unit → F := fun _ => y
  have hv : AlgebraicIndependent k v := algebraicIndependent_unique_type_iff.mpr hx
  have hw : AlgebraicIndependent k w := algebraicIndependent_unique_type_iff.mpr hy
  let A := IntermediateField.adjoin k (Set.range v)
  let φ : A →+* F := (IsFractionRing.lift
    (algebraicIndependent_iff_injective_aeval.mp hw)).comp hv.reprField.toRingHom
  let a : A := ⟨x,IntermediateField.subset_adjoin k (Set.range v) ⟨(),rfl⟩⟩
  have hφ : φ a=y := by
    let q : FractionRing (MvPolynomial Unit k) := algebraMap (MvPolynomial Unit k) _ (MvPolynomial.X ())
    have ha : hv.aevalEquivField q=a := by
      apply Subtype.ext
      rw [hv.aevalEquivField_algebraMap_apply_coe]
      simp only [MvPolynomial.aeval_X]
      rfl
    rw [←ha]
    change IsFractionRing.lift (algebraicIndependent_iff_injective_aeval.mp hw)
      (hv.aevalEquivField.symm (hv.aevalEquivField q))=y
    rw [hv.aevalEquivField.symm_apply_apply]
    simp only [q,IsFractionRing.lift_algebraMap]
    exact MvPolynomial.aeval_X w ()
  obtain ⟨f,hf⟩ := exists_extension_of_countable (k:=A) (K:=K) φ
  refine ⟨f,?_⟩
  exact (RingHom.congr_fun hf a).trans hφ

lemma exists_complex_embedding_norm_gt_one {K : Type} [Field K] [CharZero K] [Countable K]
    (x : K) (hx : Transcendental ℚ x) : ∃ f : K →+* ℂ, 1<‖f x‖ := by
  let : Uncountable ℂ := uncountable_complete_normed_field ℂ
  obtain ⟨y,hy,hyNorm⟩ := exists_transcendental_complex_norm_gt_one
  obtain ⟨f,hf⟩ := exists_embedding_sending_transcendental x hx y hy
  exact ⟨f,hf ▸ hyNorm⟩

end CriticalPercolation.Arithmetic
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_PadicDetection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Cardinal Polynomial
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma rat_exists_prime_norm_gt_one (q : ℚ) (hq : q.den≠1) :
    ∃ p : ℕ, p.Prime ∧ 1<padicNorm p q := by
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hq
  let : Fact p.Prime := ⟨hp⟩
  have hpn : ¬p∣q.num.natAbs := by
    intro hd
    have hh := Nat.dvd_gcd hd hpd
    rw [q.reduced] at hh
    exact hp.not_dvd_one hh
  have hnum : padicNorm p (q.num:ℚ)=1 :=
    (padicNorm.int_eq_one_iff _).mpr (by simpa only [Int.natCast_dvd] using hpn)
  have hden : padicNorm p (q.den:ℚ)<1 := (padicNorm.nat_lt_one_iff _).mpr hpd
  have hpos : 0<padicNorm p (q.den:ℚ) := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm
    (padicNorm.nonzero (by exact_mod_cast q.den_nz)))
  refine ⟨p,hp,?_⟩
  conv_rhs => rw [←Rat.num_div_den q]
  rw [padicNorm.div,hnum]
  exact (one_lt_div hpos).mpr (by simpa only [one_mul] using hden)

lemma rat_integer_of_all_padic_norm_le_one (q : ℚ)
    (h : ∀ p : ℕ, p.Prime → padicNorm p q≤1) : ∃ z : ℤ, (z:ℚ)=q := by
  have hd : q.den=1 := by
    by_contra hn
    obtain ⟨p,hp,hpq⟩ := rat_exists_prime_norm_gt_one q hn
    exact hpq.not_ge (h p hp)
  exact ⟨q.num,by simpa only [hd,Nat.cast_one,div_one] using (Rat.num_div_den q)⟩

lemma coeff_norm_le_one_of_roots {F : Type*} [NormedField F]
    (hna : IsNonarchimedean (norm : F → ℝ)) (P : F[X]) (hm : P.Monic) (hs : P.Splits)
    (hr : ∀ z∈P.roots, ‖z‖≤1) (i : ℕ) : ‖P.coeff i‖≤1 := by
  let R : Subring F := {
    carrier := {z | ‖z‖≤1}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := fun hx hy => (hna _ _).trans (max_le hx hy)
    mul_mem' := fun hx hy => by
      change ‖_ * _‖≤1
      rw [norm_mul]
      exact (mul_le_mul hx hy (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    neg_mem' := fun hx => by simpa only [Set.mem_ofPred_eq,norm_neg] using hx }
  have hP := hs.mem_lift_of_roots_mem_range hm R.subtype (fun z hz => ⟨⟨z,hr z hz⟩,rfl⟩)
  obtain ⟨Q,hQ⟩ := hP
  change Q.map R.subtype=P at hQ
  rw [←hQ,coeff_map]
  exact (Q.coeff i).property

lemma integral_of_all_padic_embeddings {A : Type} [Field A] [NumberField A] (x : A)
    (h : ∀ (p : ℕ) (_ : Fact p.Prime) (f : A →+* AlgebraicClosure (Padic p)),
      spectralNorm (Padic p) (AlgebraicClosure (Padic p)) (f x)≤1) : IsIntegral ℤ x := by
  have hcoeff : ∀ i, ∃ z : ℤ, (z:ℚ)=(minpoly ℚ x).coeff i := by
    intro i
    apply rat_integer_of_all_padic_norm_le_one
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    let F := AlgebraicClosure (Padic p)
    let : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField (Padic p) F
    let : NormedAlgebra (Padic p) F := spectralNorm.normedAlgebra (Padic p) F
    have hh : ‖((minpoly ℚ x).map (algebraMap ℚ F)).coeff i‖≤1 := by
      apply coeff_norm_le_one_of_roots (isNonarchimedean_spectralNorm (K:=Padic p) (L:=F))
        _ ((minpoly.monic (Algebra.IsSeparable.isIntegral ℚ x)).map _) (IsAlgClosed.splits _)
      intro z hz
      have hroot : z∈(minpoly ℚ x).rootSet F := by
        exact Multiset.mem_toFinset.mpr hz
      obtain ⟨f,hf⟩ := (NumberField.Embeddings.range_eval_eq_rootSet_minpoly A F x).symm.subset hroot
      rw [←hf]
      exact h p inferInstance f
    have he : ‖algebraMap ℚ F ((minpoly ℚ x).coeff i)‖ =
        (padicNorm p ((minpoly ℚ x).coeff i):ℝ) := by
      rw [IsScalarTower.algebraMap_apply ℚ (Padic p) F,norm_algebraMap']
      exact Padic.eq_padicNorm _
    rw [coeff_map,he] at hh
    exact_mod_cast hh
  have hl : minpoly ℚ x ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro i
    exact hcoeff i
  obtain ⟨P,hP⟩ := hl
  change P.map (Int.castRingHom ℚ)=minpoly ℚ x at hP
  refine ⟨P,?_,?_⟩
  · apply Polynomial.monic_of_injective (f:=Int.castRingHom ℚ) (Int.cast_injective (α:=ℚ))
    simpa only [hP] using minpoly.monic (Algebra.IsSeparable.isIntegral ℚ x)
  · change Polynomial.aeval x P=0
    rw [←Polynomial.aeval_map_algebraMap ℚ]
    change Polynomial.aeval x (P.map (Int.castRingHom ℚ))=0
    rw [hP]
    exact minpoly.aeval ℚ x

end CriticalPercolation.Arithmetic
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_AllPlaceKronecker
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Cardinal Polynomial
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma algebraic_of_all_complex_embeddings_bounded {K : Type} [Field K] [CharZero K]
    [Countable K] (x : K) (h : ∀ f : K →+* ℂ, ‖f x‖≤1) : IsAlgebraic ℚ x := by
  by_contra hn
  obtain ⟨f,hf⟩ := exists_complex_embedding_norm_gt_one x hn
  exact hf.not_ge (h f)

lemma uncountable_padic_closure (p : ℕ) [Fact p.Prime] :
    Uncountable (AlgebraicClosure (Padic p)) := by
  let : Uncountable (Padic p) := uncountable_complete_normed_field (Padic p)
  exact (algebraMap (Padic p) (AlgebraicClosure (Padic p))).injective.uncountable

lemma root_of_unity_of_all_places {K : Type} [Field K] [CharZero K] [Countable K]
    (x : K) (hx : x≠0)
    (hc : ∀ f : K →+* ℂ, ‖f x‖≤1)
    (hp : ∀ (p : ℕ) (_ : Fact p.Prime) (f : K →+* AlgebraicClosure (Padic p)),
      spectralNorm (Padic p) (AlgebraicClosure (Padic p)) (f x)≤1) :
    ∃ n : ℕ, 0<n ∧ x^n=1 := by
  have halg : IsAlgebraic ℚ x := algebraic_of_all_complex_embeddings_bounded x hc
  let A := IntermediateField.adjoin ℚ ({x}:Set K)
  let : FiniteDimensional ℚ A := IntermediateField.adjoin.finiteDimensional halg.isIntegral
  let : NumberField A := ⟨⟩
  let a : A := ⟨x,IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton x)⟩
  have hcA : ∀ f : A →+* ℂ, ‖f a‖≤1 := by
    intro f
    let : Uncountable ℂ := uncountable_complete_normed_field ℂ
    obtain ⟨g,hg⟩ := exists_extension_of_countable (K:=K) f
    have he : g x=f a := RingHom.congr_fun hg a
    exact he ▸ hc g
  have hi : IsIntegral ℤ a := by
    apply integral_of_all_padic_embeddings
    intro p hp' f
    let : Fact p.Prime := hp'
    let : Uncountable (AlgebraicClosure (Padic p)) := uncountable_padic_closure p
    obtain ⟨g,hg⟩ := exists_extension_of_countable (K:=K) f
    have he : g x=f a := RingHom.congr_fun hg a
    exact he ▸ hp p hp' g
  obtain ⟨n,hn,he⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one A ℂ
    (x:=a) (fun hz => hx (congrArg Subtype.val hz)) hi hcA
  exact ⟨n,hn,congrArg Subtype.val he⟩

end CriticalPercolation.Arithmetic
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_CongruenceTorsion
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped BigOperators

namespace CriticalPercolation.LinearGrowth
variable {R : Type*} [CommRing R]

lemma one_add_pow_of_sq_zero {B : Type*} [Ring B] (b : B) (hb : b*b=0) (q : ℕ) :
    (1+b)^q=1+q•b := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ,ih,add_mul,one_mul,smul_mul_assoc,mul_add,mul_one,hb,add_zero,
      add_nsmul,one_nsmul]
    abel

lemma scalar_inverse_mod (I : Ideal R) [I.IsMaximal] (q : ℕ) (hq : (q:R)∉I) :
    ∃ r : R, 1-r*(q:R)∈I := by
  let := Ideal.Quotient.field I
  have hqn : Ideal.Quotient.mk I (q:R)≠0 := by exact mt Ideal.Quotient.eq_zero_iff_mem.mp hq
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk I (q:R))⁻¹)
  refine ⟨r,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [map_sub,map_one,map_mul,hr,inv_mul_cancel₀ hqn,sub_self]

lemma congruence_power_step {n : Type*} [Fintype n] [DecidableEq n]
    (I : Ideal R) [I.IsMaximal] (A : Matrix n n R) (k q : ℕ)
    (hk : 1≤k) (hq : (q:R)∉I) (hpow : A^q=1)
    (hA : ∀ i j, (A-1) i j∈I^k) : ∀ i j, (A-1) i j∈I^(k+1) := by
  let J := I^(k+1)
  let f := (Ideal.Quotient.mk J).mapMatrix (m:=n)
  let B := A-1
  have hsquare : f (B*B)=0 := by
    ext i j
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (∑ l, B i l*B l j)∈I^(k+1)
    apply Ideal.sum_mem
    intro l hl
    apply Ideal.pow_le_pow_right (show k+1≤k+k by omega)
    rw [pow_add]
    exact Ideal.mul_mem_mul (hA i l) (hA l j)
  have hsquare' : f B*f B=0 := by simpa using hsquare
  have hsum : 1+q•f B=1 := by
    rw [←one_add_pow_of_sq_zero (f B) hsquare']
    have he : 1+f B=f A := by dsimp only [B]; rw [map_sub,map_one]; abel
    rw [he,←map_pow,hpow,map_one]
  have hz : q•f B=0 := add_left_cancel (hsum.trans (add_zero _).symm)
  have hqB (i j) : (q:R)*B i j∈J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg (fun M : Matrix n n (R ⧸ J) => M i j) hz
    simpa [f,nsmul_eq_mul,map_mul] using he
  obtain ⟨r,hr⟩ := scalar_inverse_mod I q hq
  intro i j
  have h1 := J.mul_mem_left r (hqB i j)
  have h2 : (1-r*(q:R))*B i j∈J := by
    change _∈I^(k+1)
    rw [pow_succ']
    exact Ideal.mul_mem_mul hr (hA i j)
  have h := J.add_mem h1 h2
  convert h using 1 <;> first | rfl | ring

lemma eq_one_of_prime_to_residue_order {n : Type*} [Fintype n] [DecidableEq n]
    [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [I.IsMaximal]
    (A : Matrix n n R) (q : ℕ) (hq : (q:R)∉I) (hpow : A^q=1)
    (hA : ∀ i j, (A-1) i j∈I) : A=1 := by
  have hall (k : ℕ) : ∀ i j, (A-1) i j∈I^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases hk : k=0
      · simpa [hk] using hA
      · exact congruence_power_step I A k q (by omega) hq hpow ih
  have he (i j) : (A-1) i j=0 := by
    have hm : (A-1) i j∈⨅ k : ℕ, I^k := by simpa using (fun k => hall k i j)
    rw [Ideal.iInf_pow_eq_bot_of_isDomain I (Ideal.IsMaximal.ne_top inferInstance)] at hm
    exact hm
  exact sub_eq_zero.mp (Matrix.ext he)

lemma int_isJacobsonRing : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  by_cases hP0 : P=⊥
  · subst P
    apply le_antisymm _ Ideal.le_jacobson
    intro x hx
    obtain ⟨z,hz⟩ := Ideal.mem_jacobson_iff.mp hx (3*x)
    change z*(3*x)*x+z-1=0 at hz
    have hu : IsUnit (3*x*x+1) := ⟨⟨3*x*x+1,z,by nlinarith [hz],by nlinarith [hz]⟩,rfl⟩
    rcases Int.isUnit_iff.mp hu with h|h <;> change x=0 <;> nlinarith [sq_nonneg x]
  · let : P.IsPrime := hP
    let : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
    exact Ideal.jacobson_eq_self_of_isMaximal

lemma finite_field_of_finiteType_int (F : Type*) [Field F] [a : Algebra ℤ F] [Algebra.FiniteType ℤ F] :
    Finite F := by
  cases Subsingleton.elim a (Ring.toIntAlgebra F)
  let : IsJacobsonRing ℤ := int_isJacobsonRing
  let : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  let J : Ideal ℤ := Ideal.under ℤ (⊥ : Ideal F)
  have hJ : J.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (⊥ : Ideal F)
  have hJ0 : J≠⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hJ Int.not_isField
  let : Finite (ℤ ⧸ J) := Ring.HasFiniteQuotients.finiteQuotient hJ0
  let : Module.Finite (ℤ ⧸ J) (F ⧸ (⊥ : Ideal F)) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  let : Finite (F ⧸ (⊥ : Ideal F)) := Module.finite_of_finite (ℤ ⧸ J)
  exact Finite.of_injective (Ideal.Quotient.mk (⊥ : Ideal F)) (by
    intro x y h
    exact sub_eq_zero.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).mp h))

lemma finite_residue_of_finiteType_int [Algebra.FiniteType ℤ R]
    (I : Ideal R) [I.IsMaximal] : Finite (R ⧸ I) := by
  let := Ideal.Quotient.field I
  let : Algebra.FiniteType ℤ (R ⧸ I) := Algebra.FiniteType.quotient ℤ I
  exact finite_field_of_finiteType_int (R ⧸ I)

lemma exists_maximal_avoiding [IsDomain R] [IsJacobsonRing R] (x : R) (hx : x≠0) :
    ∃ I : Ideal R, I.IsMaximal ∧ x∉I := by
  by_contra! h
  have hm : x∈(⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson,Submodule.mem_sInf]
    exact fun I hI => h I hI.2
  rw [IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)] at hm
  exact hx hm

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FgMatrixRing
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.LinearGrowth
variable {G R : Type*} [Group G] [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma exists_finiteType_matrix_ring [Group.FG G] (ρ : G →* GL n R) :
    ∃ D : Subalgebra ℤ R, Algebra.FiniteType ℤ D ∧ ∀ g i j, ρ g i j∈D := by
  obtain ⟨S,hS,hSf⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let T := hSf.toFinset ∪ hSf.toFinset⁻¹
  let E := T.biUnion (fun g => Finset.univ.biUnion (fun i => Finset.univ.image (fun j => ρ g i j)))
  let D := Algebra.adjoin ℤ (E : Set R)
  have hD : Algebra.FiniteType ℤ D := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset E)
  have hgen (g : G) (hg : g∈T) (i j : n) : ρ g i j∈D := by
    apply Algebra.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩⟩
  refine ⟨D,hD,?_⟩
  intro g
  have hg : g∈Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction'' with
  | mem a ha => exact hgen a (Finset.mem_union_left _ (hSf.mem_toFinset.mpr ha))
  | inv_mem a ha =>
    apply hgen a⁻¹
    apply Finset.mem_union_right
    simpa using hSf.mem_toFinset.mpr ha
  | one =>
    intro i j
    rw [map_one]
    by_cases h : i=j <;> simp [h,D.zero_mem,D.one_mem]
  | mul a b ha hb iha ihb =>
    intro i j
    rw [map_mul]
    change (∑ l, ρ a i l*ρ b l j)∈D
    exact D.sum_mem (fun l _ => D.mul_mem (iha i l) (ihb l j))

variable (ρ : G →* GL n R) (D : Subalgebra ℤ R) (hD : ∀ g i j, ρ g i j∈D)

lemma liftMatrixGroup_injective (hρ : Injective ρ) : Injective (liftMatrixGroup ρ D hD) := by
  intro x y he
  apply hρ
  apply Units.ext
  ext i j
  exact congrArg (fun M : GL n D => ((M i j : D) : R)) he

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_PeriodicSpectrum
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth

lemma multiset_prod_dvd_pow_card {R : Type*} [CommMonoid R] (s : Multiset R) (a : R)
    (h : ∀ b∈s, b∣a) : s.prod∣a^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    simp only [Multiset.prod_cons,Multiset.card_cons,pow_succ']
    exact mul_dvd_mul (h b (Multiset.mem_cons_self _ _))
      (ih (fun c hc => h c (Multiset.mem_cons_of_mem hc)))

lemma nilpotent_aeval_of_vanishing_roots {K R : Type*} [Field K] [Ring R] [Algebra K R]
    (a : R) (hp : (minpoly K a).Monic) (hs : (minpoly K a).Splits)
    (q : K[X]) (hq : ∀ x ∈ (minpoly K a).roots, q.IsRoot x) : IsNilpotent (aeval a q) := by
  have hd : minpoly K a ∣ q^(minpoly K a).roots.card := by
    nth_rw 1 [hs.eq_prod_roots_of_monic hp]
    convert multiset_prod_dvd_pow_card ((minpoly K a).roots.map (fun x => X-C x)) q ?_ using 1
    · simp only [Multiset.card_map]
    · intro b hb
      obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hb
      exact dvd_iff_isRoot.mpr (hq x hx)
  exact ⟨_,by rw [←map_pow]; exact minpoly.dvd_iff.mp hd⟩

lemma exists_scalar_unipotent_power {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : End K V) (a : K) (ha : a≠0)
    (hr : ∀ r, (minpoly K A).IsRoot r → ∃ m : ℕ, 0 < m ∧ (r/a)^m=1) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (A^m-a^m • (1:End K V)) := by
  let s := (minpoly K A).roots.toFinset
  have he (r : s) : ∃ m : ℕ, 0 < m ∧ (r.val/a)^m=1 :=
    hr r.val (isRoot_of_mem_roots (Multiset.mem_toFinset.mp r.property))
  choose m hm hm1 using he
  let N := ∏ r : s, m r
  have hN : 0 < N := Finset.prod_pos (fun r _ => hm r)
  have hpow (r : s) : (r.val/a)^N=1 := by
    have hd : m r∣N := Finset.dvd_prod_of_mem m (Finset.mem_univ r)
    obtain ⟨k,hk⟩ := hd
    rw [hk,pow_mul,hm1 r,one_pow]
  refine ⟨N,hN,?_⟩
  have hn := nilpotent_aeval_of_vanishing_roots A (minpoly.monic (Algebra.IsIntegral.isIntegral A))
    (IsAlgClosed.splits (minpoly K A)) (X^N-C (a^N)) ?_
  · simpa only [map_sub,map_pow,aeval_X,aeval_C,Algebra.algebraMap_eq_smul_one,_root_.smul_pow,one_pow] using hn
  · intro r hr'
    have hrN := hpow ⟨r,Multiset.mem_toFinset.mpr hr'⟩
    have hep : r^N=a^N := by
      apply (div_eq_one_iff_eq (pow_ne_zero _ ha)).mp
      simpa only [div_pow] using hrN
    simp only [IsRoot,eval_sub,eval_pow,eval_X,eval_C,hep,sub_self]

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_PowerBoundedUnipotent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Function

namespace CriticalPercolation.LinearGrowth
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

lemma eq_zero_of_bounded_nat_multiples (x : R) (C : ℝ)
    (h : ∀ n : ℕ, ‖(n:ℝ) • x‖≤C) : x=0 := by
  by_contra hx
  have hxpos : 0<‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨n,hn⟩ := exists_nat_gt (C/‖x‖)
  have hh := h n
  rw [norm_smul,Real.norm_natCast] at hh
  exact ((div_lt_iff₀ hxpos).mp hn).not_ge hh

lemma pow_mul_of_affine_step (a b c : R) (hab : a*b=b+c) (hac : a*c=c) :
    ∀ n : ℕ, a^n*b=b+(n:ℝ) • c := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_assoc,ih,mul_add,mul_smul_comm,hab,hac]
    simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    abel

lemma eq_one_of_power_bounded_unipotent (a : R) (hni : IsNilpotent (a-1))
    (C : ℝ) (hb : ∀ n : ℕ, ‖a^n‖≤C) : a=1 := by
  let N := a-1
  have hdrop : ∀ k : ℕ, N^k=0 → N=0 := by
    intro k
    induction k with
    | zero =>
      intro hz
      have ho : (1:R)=0 := by simpa only [pow_zero] using hz
      exact (mul_one N).symm.trans ((congrArg (N*·) ho).trans (mul_zero N))
    | succ k ih =>
      intro hz
      by_cases hk : k=0
      · simpa only [hk,zero_add,pow_one] using hz
      have hp : 1≤k := Nat.one_le_iff_ne_zero.mpr hk
      let b := N^(k-1)
      let c := N^k
      have hab : a*b=b+c := by
        have he : a=1+N := by dsimp [N]; noncomm_ring
        rw [he,add_mul,one_mul]
        congr 1
        dsimp [b,c]
        rw [←pow_succ',Nat.sub_add_cancel hp]
      have hac : a*c=c := by
        have he : a=1+N := by dsimp [N]; noncomm_ring
        rw [he,add_mul,one_mul]
        have hn : N*c=0 := by simpa only [c,←pow_succ'] using hz
        rw [hn,add_zero]
      have he : c=0 := by
        apply eq_zero_of_bounded_nat_multiples c ((C+1)*‖b‖)
        intro n
        have heq : (n:ℝ) • c=a^n*b-b := by
          rw [pow_mul_of_affine_step a b c hab hac n,add_sub_cancel_left]
        rw [heq]
        calc
          ‖a^n*b-b‖ ≤ ‖a^n*b‖+‖b‖ := norm_sub_le _ _
          _ ≤ C*‖b‖+‖b‖ := add_le_add ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))) le_rfl
          _ = (C+1)*‖b‖ := by ring
      exact ih he
  obtain ⟨k,hk⟩ := hni
  exact sub_eq_zero.mp (hdrop k hk)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ProjectiveEigenvalues
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Function

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V] [Group G]

lemma equiv_eigenvalue_ne_zero (T : V ≃L[K] V) {v : V} (hv : v≠0) {a : K}
    (he : T v=a • v) : a≠0 := by
  intro ha
  apply hv
  apply T.injective
  simpa only [ha,zero_smul,map_zero] using he

lemma representation_pow_eigenvector (ρ : G →* (V ≃L[K] V)) (g : G)
    {v : V} {a : K} (he : ρ g v=a • v) (n : ℕ) : ρ (g^n) v=a^n • v := by
  induction n with
  | zero => rw [pow_zero,map_one,pow_zero,one_smul]; rfl
  | succ n ih =>
    rw [pow_succ,map_mul]
    change ρ (g^n) (ρ g v)=_
    rw [he,map_smul,ih,smul_smul]
    congr 1
    rw [pow_succ,mul_comm]

lemma eigenvalue_ratio_norm_le_one (ρ : G →* (V ≃L[K] V))
    (δ : ℝ) (hδ : 0<δ)
    (hb : ∀ g : G, ∀ x : V, δ*‖(ρ g).toContinuousLinearMap‖*‖x‖≤‖ρ g x‖)
    (g : G) {v w : V} (hv : v≠0) (hw : w≠0) {a b : K}
    (ha : ρ g v=a • v) (hb' : ρ g w=b • w) : ‖a/b‖≤1 := by
  have hb0 : b≠0 := equiv_eigenvalue_ne_zero _ hw hb'
  have hvp : 0<‖v‖ := norm_pos_iff.mpr hv
  have hwp : 0<‖w‖ := norm_pos_iff.mpr hw
  have hbp : 0<‖b‖ := norm_pos_iff.mpr hb0
  have hpow (n : ℕ) : ‖a/b‖^n≤1/δ := by
    have hu := (ρ (g^n)).toContinuousLinearMap.le_opNorm v
    change ‖ρ (g^n) v‖≤‖(ρ (g^n)).toContinuousLinearMap‖*‖v‖ at hu
    rw [representation_pow_eigenvector ρ g ha n,norm_smul,norm_pow] at hu
    have hu' : ‖a‖^n≤‖(ρ (g^n)).toContinuousLinearMap‖ := (mul_le_mul_iff_left₀ hvp).mp hu
    have hl := hb (g^n) w
    rw [representation_pow_eigenvector ρ g hb' n,norm_smul,norm_pow] at hl
    have hl' : δ*‖(ρ (g^n)).toContinuousLinearMap‖≤‖b‖^n := (mul_le_mul_iff_left₀ hwp).mp hl
    rw [norm_div,div_pow]
    apply (div_le_div_iff₀ (pow_pos hbp n) hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hu' hδ.le]
  by_contra hn
  obtain ⟨n,hn'⟩ := pow_unbounded_of_one_lt (1/δ) (lt_of_not_ge hn)
  exact hn'.not_ge (hpow n)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ProjectivePeriodicity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Module

namespace CriticalPercolation.LinearGrowth
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma scalar_power_of_projective_bound (T : V →L[ℂ] V)
    (δ : ℝ) (hδ : 0<δ)
    (hb : ∀ n : ℕ, ∀ x : V, δ*‖T^n‖*‖x‖≤‖(T^n) x‖)
    {v : V} (hv : v≠0) {a : ℂ} (ha : a≠0) (he : T v=a • v)
    (m : ℕ) (hni : IsNilpotent (T^m-a^m • (1:V →L[ℂ] V))) :
    T^m=a^m • (1:V →L[ℂ] V) := by
  let U := (a^m)⁻¹ • T^m
  have hU : IsNilpotent (U-1) := by
    have hh := hni.smul ((a^m)⁻¹)
    simpa only [U,smul_sub,smul_smul,inv_mul_cancel₀ (pow_ne_zero m ha),one_smul] using hh
  have hepow (n : ℕ) : (T^n) v=a^n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change T ((T^n) v)=_
      rw [ih,map_smul,he,smul_smul,pow_succ]
  have hnorm (n : ℕ) : δ*‖T^n‖≤‖a‖^n := by
    have hh := hb n v
    rw [hepow,norm_smul,norm_pow a n] at hh
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp hh
  have hUb (n : ℕ) : ‖U^n‖≤1/δ := by
    dsimp [U]
    rw [smul_pow,norm_smul,norm_pow ((a^m)⁻¹) n,norm_inv,norm_pow a m,inv_pow,←pow_mul,←pow_mul]
    have hh := hnorm (m*n)
    have hpos : 0<‖a‖^(m*n) := pow_pos (norm_pos_iff.mpr ha) _
    rw [inv_mul_eq_div]
    apply (div_le_div_iff₀ hpos hδ).mpr
    nlinarith
  have hU1 : U=1 := eq_one_of_power_bounded_unipotent U hU (1/δ) hUb
  have hh := congrArg (fun x : V →L[ℂ] V => a^m • x) hU1
  simpa only [U,smul_smul,mul_inv_cancel₀ (pow_ne_zero m ha),one_smul] using hh

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_SelbergCongruence
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

lemma gl_eq_one_of_prime_to_residue_order [IsDomain R] [IsNoetherianRing R]
    (I : Ideal R) [I.IsMaximal] (g : GL n R) (q : ℕ) (hq : (q:R)∉I)
    (hpow : g^q=1) (hmod : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g=1) :
    g=1 := by
  apply Units.ext
  apply eq_one_of_prime_to_residue_order I g.val q hq
  · exact congrArg Units.val hpow
  · intro i j
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg (fun M : GL n (R ⧸ I) => M i j) hmod
    rw [Matrix.GeneralLinearGroup.map_apply] at he
    have he1 : (Ideal.Quotient.mk I) ((1 : Matrix n n R) i j)=(1 : Matrix n n (R ⧸ I)) i j := by
      by_cases h : i=j <;> simp [Matrix.one_apply,h]
    change (Ideal.Quotient.mk I) (g.val i j-(1 : Matrix n n R) i j)=0
    rw [map_sub,he1,he]
    simp

lemma eq_one_of_no_prime_order {G : Type*} [Group G]
    (h : ∀ (g : G) (p : ℕ), p.Prime → g^p=1 → g=1)
    (g : G) (hg : IsOfFinOrder g) : g=1 := by
  by_contra hne
  have ho : orderOf g≠1 := by simpa using hne
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd ho
  let y := g^(orderOf g/p)
  have hyord : orderOf y=p := orderOf_pow_orderOf_div hg.orderOf_pos.ne' hpd
  have hy : y^p=1 := hyord ▸ pow_orderOf_eq_one y
  have he := h y p hp hy
  have he1 : p=1 := by simpa [he] using hyord.symm
  exact hp.ne_one he1

theorem exists_finiteIndex_no_finite_order [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] :
    ∃ H : Subgroup (GL n R), H.Normal ∧ H.FiniteIndex ∧
      ∀ h : H, IsOfFinOrder h → h=1 := by
  let : IsJacobsonRing ℤ := int_isJacobsonRing
  let : IsJacobsonRing R := isJacobsonRing_of_finiteType (A:=ℤ) (B:=R)
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let : I.IsMaximal := hI
  let := Ideal.Quotient.field I
  let : Finite (R ⧸ I) := finite_residue_of_finiteType_int I
  let p := ringChar (R ⧸ I)
  have hp : p.Prime := CharP.char_is_prime (R ⧸ I) p
  obtain ⟨J,hJ,hpJ⟩ := exists_maximal_avoiding (p:R) (Nat.cast_ne_zero.mpr hp.ne_zero)
  let : J.IsMaximal := hJ
  let : Finite (R ⧸ J) := finite_residue_of_finiteType_int J
  let f := (Matrix.GeneralLinearGroup.map (n:=n) (Ideal.Quotient.mk I)).prod
    (Matrix.GeneralLinearGroup.map (n:=n) (Ideal.Quotient.mk J))
  let H := f.ker
  refine ⟨H,inferInstance,Subgroup.finiteIndex_ker f,?_⟩
  apply eq_one_of_no_prime_order
  intro g q hq hpow
  have hmods := g.property
  change (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g.val,
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) g.val)=(1,1) at hmods
  apply Subtype.ext
  change g.val=1
  have hpow' : g.val^q=1 := congrArg Subtype.val hpow
  by_cases hqp : q=p
  · subst q
    exact gl_eq_one_of_prime_to_residue_order J g.val p hpJ hpow' (congrArg Prod.snd hmods)
  · have hqI : (q:R)∉I := by
      intro hm
      have hc : (q:R ⧸ I)=0 := by simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hm
      have hd : p∣q := (CharP.cast_eq_zero_iff (R ⧸ I) p q).mp hc
      rcases (Nat.dvd_prime hq).mp hd with he|he
      · exact hp.ne_one he
      · exact hqp he.symm
    exact gl_eq_one_of_prime_to_residue_order I g.val q hqI hpow' (congrArg Prod.fst hmods)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_SelbergSchur
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {G R : Type*} [Group G] [CommRing R] [IsDomain R] [CharZero R]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem finiteIndex_no_finite_order_of_faithful [Group.FG G]
    (ρ : G →* GL n R) (hρ : Injective ρ) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∀ h : H, IsOfFinOrder h → h=1 := by
  obtain ⟨D,hD,hm⟩ := exists_finiteType_matrix_ring ρ
  let : Algebra.FiniteType ℤ D := hD
  let φ := liftMatrixGroup ρ D hm
  have hφ : Injective φ := liftMatrixGroup_injective ρ D hm hρ
  obtain ⟨K,hKn,hKi,hKt⟩ := exists_finiteIndex_no_finite_order (R:=D) (n:=n)
  let : K.Normal := hKn
  let H := K.comap φ
  have hHi : H.FiniteIndex := by
    constructor
    rw [Subgroup.index_comap]
    intro hz
    exact hKi.index_ne_zero (Nat.eq_zero_of_zero_dvd (hz ▸ K.relIndex_dvd_index_of_normal φ.range))
  let ψ : H →* K := (φ.comp H.subtype).codRestrict K (fun h => h.property)
  refine ⟨H,inferInstance,hHi,?_⟩
  intro h hh
  have hψ : IsOfFinOrder (ψ h) := by
    obtain ⟨m,hm,he⟩ := hh.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,by rw [←map_pow,he,map_one]⟩
  have he : ψ h=1 := hKt _ hψ
  apply Subtype.ext
  apply hφ
  exact (congrArg Subtype.val he).trans φ.map_one.symm

theorem finite_of_torsion_faithful [Group.FG G] (ρ : G →* GL n R) (hρ : Injective ρ)
    (ht : ∀ g : G, IsOfFinOrder g) : Finite G := by
  obtain ⟨H,hHn,hHi,hHt⟩ := finiteIndex_no_finite_order_of_faithful ρ hρ
  have hsub : Subsingleton H := by
    constructor
    intro x y
    have htx : IsOfFinOrder x := H.subtype_injective.isOfFinOrder_iff.mp (ht x)
    have hty : IsOfFinOrder y := H.subtype_injective.isOfFinOrder_iff.mp (ht y)
    exact (hHt _ htx).trans (hHt _ hty).symm
  let : Subsingleton H := hsub
  exact H.finite_iff_finite_and_finiteIndex.mpr ⟨inferInstance,hHi⟩

theorem finite_range_of_torsion [Group.FG G] (ρ : G →* GL n R)
    (ht : ∀ g : G, IsOfFinOrder (ρ g)) : Finite ρ.range := by
  let : Group.FG ρ.range := Group.fg_of_surjective ρ.rangeRestrict_surjective
  apply finite_of_torsion_faithful ρ.range.subtype ρ.range.subtype_injective
  intro g
  obtain ⟨x,hx⟩ := g.property
  apply ρ.range.subtype_injective.isOfFinOrder_iff.mp
  change IsOfFinOrder (g : GL n R)
  rw [←hx]
  exact ht x

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ProjectivelyPeriodicSchur
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Group G]

lemma finite_range_of_torsion_linearEquiv [Group.FG G] (ρ : G →* (V ≃ₗ[K] V))
    (ht : ∀ g, IsOfFinOrder (ρ g)) : Finite ρ.range := by
  let τ := linearMatrixEquiv.toMonoidHom.comp ρ
  have ht' (g : G) : IsOfFinOrder (τ g) := by
    obtain ⟨m,hm,he⟩ := (ht g).exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    change (linearMatrixEquiv (ρ g))^m=1
    rw [←map_pow,he,map_one]
  let : Finite τ.range := finite_range_of_torsion τ ht'
  let f : ρ.range → τ.range := fun x => ⟨linearMatrixEquiv x.val,by
    obtain ⟨g,hg⟩ := x.property
    exact ⟨g,congrArg linearMatrixEquiv hg⟩⟩
  exact Finite.of_injective f (fun x y h => Subtype.ext
    (linearMatrixEquiv.injective (congrArg Subtype.val h)))

omit [CharZero K] [FiniteDimensional K V] in
lemma conjugation_eq_one_of_scalar (e : V ≃ₗ[K] V) (c : K)
    (hc : e.toLinearMap=c • (1:End K V)) : e.conj=1 := by
  have he (x : V) : e x=c • x := congrArg (fun f : End K V => f x) hc
  ext f x
  change e (f (e.symm x))=f x
  rw [he,←f.map_smul,←he,e.apply_symm_apply]

lemma exists_finiteIndex_comm_range_of_projectively_periodic [Group.FG G]
    (ρ : G →* (V ≃ₗ[K] V))
    (ht : ∀ g, ∃ m : ℕ, 0 < m ∧ ∃ c : K,
      ((ρ g).toLinearMap)^m=c • (1:End K V)) :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∀ x y : (ρ.comp H.subtype).range, x*y=y*x := by
  let τ := conjugationRepresentation ρ
  have htτ (g : G) : IsOfFinOrder (τ g) := by
    obtain ⟨m,hm,c,hc⟩ := ht g
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    rw [←map_pow]
    apply conjugation_eq_one_of_scalar (ρ (g^m)) c
    rw [map_pow]
    change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (ρ g^m))=_
    rw [map_pow]
    exact hc
  let : Finite τ.range := finite_range_of_torsion_linearEquiv τ htτ
  refine ⟨τ.ker,inferInstance,?_⟩
  intro x y
  obtain ⟨g,hg⟩ := x.property
  obtain ⟨h,hh⟩ := y.property
  apply Subtype.ext
  change x.val*y.val=y.val*x.val
  rw [←hg,←hh]
  have hconj : (ρ g.val).conj=1 := g.property
  ext v
  have he := congrArg (fun e : End K V ≃ₗ[K] End K V => e (ρ h.val).toLinearMap (ρ g.val v)) hconj
  change (ρ g.val) ((ρ h.val) v)=(ρ h.val) ((ρ g.val) v)
  change (ρ g.val) ((ρ h.val) ((ρ g.val).symm ((ρ g.val) v)))=(ρ h.val) ((ρ g.val) v) at he
  simpa only [LinearEquiv.conj_apply_apply,LinearEquiv.symm_apply_apply,
    LinearEquiv.coe_one,id_eq,LinearEquiv.mul_apply,MonoidHom.comp_apply,Subgroup.coe_subtype] using he

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ProperPadicModels
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma exists_finite_padic_matrix_model {G n : Type} [Group G] [Group.FG G]
    [Fintype n] [DecidableEq n] (p : ℕ) [Fact p.Prime]
    (ρ : G →* GL n (AlgebraicClosure (Padic p)))
    (E : Finset (AlgebraicClosure (Padic p))) :
    ∃ L : IntermediateField (Padic p) (AlgebraicClosure (Padic p)),
      FiniteDimensional (Padic p) L ∧ (E:Set (AlgebraicClosure (Padic p)))⊆(L:Set (AlgebraicClosure (Padic p))) ∧
      ∃ τ : G →* GL n L, ∀ g,
        Matrix.GeneralLinearGroup.map L.val.toRingHom (τ g)=ρ g := by
  obtain ⟨D,hD,hm⟩ := LinearGrowth.exists_finiteType_matrix_ring ρ
  obtain ⟨F,hF⟩ := (Subalgebra.fg_iff_finiteType D).mpr hD
  let L := IntermediateField.adjoin (Padic p) (↑(F∪E):Set (AlgebraicClosure (Padic p)))
  have hfin : FiniteDimensional (Padic p) L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hDL : D≤L.toSubalgebra.restrictScalars ℤ := by
    rw [←hF]
    apply Algebra.adjoin_le
    intro x hx
    exact IntermediateField.subset_adjoin (Padic p) _ (Finset.mem_union_left _ hx)
  let τ : G →* GL n L := LinearGrowth.liftMatrixGroup ρ
    (L.toSubalgebra.restrictScalars ℤ) (fun g i j => hDL (hm g i j))
  refine ⟨L,hfin,?_,τ,?_⟩
  · intro x hx
    exact IntermediateField.subset_adjoin (Padic p) _ (Finset.mem_union_right _ hx)
  · intro g
    exact LinearGrowth.liftMatrixGroup_map ρ (L.toSubalgebra.restrictScalars ℤ) _ g

end CriticalPercolation.Arithmetic
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_StrongDenseEigenvalues
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K L T G n : Type} [Field K] [Field L] [Field T] [Group G]
variable [Fintype n] [DecidableEq n]
variable {degree : ℕ}

omit [DecidableEq n] in
lemma eigenvector_transfer (f : K →+* T) (e : L →+* T)
    (A : Matrix n n K) (B : Matrix n n L)
    (hm : ∀ i j, f (A i j)=e (B i j))
    (v : n → K) (w : n → L) (hv : ∀ i, f (v i)=e (w i))
    (a : K) (b : L) (ha : f a=e b) (hAv : A.mulVec v=a • v) : B.mulVec w=b • w := by
  have hm' : A.map f=B.map e := by ext i j; exact hm i j
  have hv' : f ∘ v=e ∘ w := funext hv
  ext i
  apply e.injective
  rw [e.map_mulVec,←hm',←hv',←f.map_mulVec,hAv]
  simp only [Pi.smul_apply,smul_eq_mul,map_mul,ha,hv]

omit [Fintype n] [DecidableEq n] in
lemma eigenvector_transfer_ne_zero (f : K →+* T) (e : L →+* T)
    (v : n → K) (w : n → L) (hv : ∀ i, f (v i)=e (w i)) (hn : v≠0) : w≠0 := by
  intro hw
  apply hn
  ext i
  apply f.injective
  simpa only [hw,Pi.zero_apply,map_zero] using hv i

lemma matrix_local_ratio_bound {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [DecidableEq G] (ρ : G →* GL n K) (hρ : StrongFullMatrixSpan ρ)
    (hg : SparseGrowth.HasPolynomialDegree G degree) (g : G)
    {v w : n → K} (hv : v≠0) (hw : w≠0) {a b : K}
    (ha : (ρ g).val.mulVec v=a • v) (hb : (ρ g).val.mulVec w=b • w) : ‖a/b‖≤1 := by
  let : Nontrivial (n → K) := ⟨⟨v,0,hv⟩⟩
  obtain ⟨S,h1,hi,hgen,hgS⟩ := (SparseGrowth.hasPolynomialDegree_iff degree).mp hg
  obtain ⟨δ,hδ,hbnd⟩ := projective_bound_of_strongFullSpan (matrixRepresentation ρ)
    (hρ.strongFullSpan ρ) S h1 hgen degree hgS
  exact eigenvalue_ratio_norm_le_one (continuousRepresentation (matrixRepresentation ρ))
    δ hδ hbnd g hv hw ha hb

lemma eigenvalue_ratio_root_of_unity_of_strongFullMatrixSpan
    [CharZero K] [Countable K] [DecidableEq G]
    (ρ : G →* GL n K) (hρ : StrongFullMatrixSpan ρ)
    (hg : SparseGrowth.HasPolynomialDegree G degree) (g : G)
    {v w : n → K} (hv : v≠0) (hw : w≠0) {a b : K}
    (ha : (ρ g).val.mulVec v=a • v) (hb : (ρ g).val.mulVec w=b • w) :
    ∃ m : ℕ, 0 < m ∧ (a/b)^m=1 := by
  have ha0 : a≠0 := by
    intro he
    have hz : (matrixRepresentation ρ g) v=(matrixRepresentation ρ g) 0 := by
      simpa only [matrixRepresentation_apply,he,zero_smul,Matrix.mulVec_zero] using ha
    exact hv ((matrixRepresentation ρ g).injective hz)
  have hb0 : b≠0 := by
    intro he
    have hz : (matrixRepresentation ρ g) w=(matrixRepresentation ρ g) 0 := by
      simpa only [matrixRepresentation_apply,he,zero_smul,Matrix.mulVec_zero] using hb
    exact hw ((matrixRepresentation ρ g).injective hz)
  apply Arithmetic.root_of_unity_of_all_places (a/b) (div_ne_zero ha0 hb0)
  · intro f
    let τ := (Matrix.GeneralLinearGroup.map f).comp ρ
    have hm : ∀ g i j, f (ρ g i j)=(RingHom.id ℂ) (τ g i j) := fun _ _ _ => rfl
    have hτ := hρ.transfer f (RingHom.id ℂ) ρ τ hm
    let v' : n → ℂ := f ∘ v
    let w' : n → ℂ := f ∘ w
    have hv' : v'≠0 := eigenvector_transfer_ne_zero f (RingHom.id ℂ) v v' (fun _ => rfl) hv
    have hw' : w'≠0 := eigenvector_transfer_ne_zero f (RingHom.id ℂ) w w' (fun _ => rfl) hw
    have ha' := eigenvector_transfer f (RingHom.id ℂ) (ρ g).val (τ g).val
      (hm g) v v' (fun _ => rfl) a (f a) rfl ha
    have hb' := eigenvector_transfer f (RingHom.id ℂ) (ρ g).val (τ g).val
      (hm g) w w' (fun _ => rfl) b (f b) rfl hb
    simpa only [map_div₀] using matrix_local_ratio_bound τ hτ hg g hv' hw' ha' hb'
  · intro p hp f
    let : Fact p.Prime := hp
    let C := AlgebraicClosure (Padic p)
    let : Group.FG G := hg.fg
    let σ := (Matrix.GeneralLinearGroup.map f).comp ρ
    let E : Finset C := {f a,f b} ∪ Finset.univ.image (f ∘ v) ∪ Finset.univ.image (f ∘ w)
    obtain ⟨L,hL,hE,τ,hτ⟩ := Arithmetic.exists_finite_padic_matrix_model p σ E
    let : FiniteDimensional (Padic p) L := hL
    let : ProperSpace L := FiniteDimensional.proper (Padic p) L
    have haL : f a∈L := hE (by simp [E])
    have hbL : f b∈L := hE (by simp [E])
    have hvL (i : n) : f (v i)∈L := hE (by simp [E,Function.comp_def])
    have hwL (i : n) : f (w i)∈L := hE (by simp [E,Function.comp_def])
    let a' : L := ⟨f a,haL⟩
    let b' : L := ⟨f b,hbL⟩
    let v' : n → L := fun i => ⟨f (v i),hvL i⟩
    let w' : n → L := fun i => ⟨f (w i),hwL i⟩
    have hm : ∀ g i j, f (ρ g i j)=L.val.toRingHom (τ g i j) := by
      intro g i j
      exact (congrArg (fun M : GL n C => M i j) (hτ g)).symm
    have hτfull := hρ.transfer f L.val.toRingHom ρ τ hm
    have hv' : v'≠0 := eigenvector_transfer_ne_zero f L.val.toRingHom v v' (fun _ => rfl) hv
    have hw' : w'≠0 := eigenvector_transfer_ne_zero f L.val.toRingHom w w' (fun _ => rfl) hw
    have ha' := eigenvector_transfer f L.val.toRingHom (ρ g).val (τ g).val
      (hm g) v v' (fun _ => rfl) a a' rfl ha
    have hb' := eigenvector_transfer f L.val.toRingHom (ρ g).val (τ g).val
      (hm g) w w' (fun _ => rfl) b b' rfl hb
    have hh := matrix_local_ratio_bound τ hτfull hg g hv' hw' ha' hb'
    change ‖((a'/b' : L) : C)‖≤1 at hh
    change ‖f (a/b)‖≤1
    simpa only [map_div₀, IntermediateField.coe_div] using hh

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_StrongDensePeriodicity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K G n : Type} [Field K] [CharZero K] [Countable K] [IsAlgClosed K]
variable [Group G] [DecidableEq G] [Fintype n] [DecidableEq n] [Nonempty n]
variable {degree : ℕ}

lemma scalar_power_of_strongFullMatrixSpan (ρ : G →* GL n K)
    (hρ : StrongFullMatrixSpan ρ) (hg : SparseGrowth.HasPolynomialDegree G degree) (g : G) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : K, a≠0 ∧ (ρ g).val^m=a • (1:Matrix n n K) := by
  let A := (matrixRepresentation ρ g).toLinearMap
  obtain ⟨a,ha⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v,hv⟩ := ha.exists_hasEigenvector
  have hav : (ρ g).val.mulVec v=a • v := hv.apply_eq_smul
  have ha0 : a≠0 := by
    intro he
    exact hv.2 ((matrixRepresentation ρ g).injective (by
      change (ρ g).val.mulVec v=(ρ g).val.mulVec 0
      simpa only [he,zero_smul,Matrix.mulVec_zero] using hav))
  obtain ⟨m,hm,hni⟩ := exists_scalar_unipotent_power A a ha0 (by
    intro r hr
    obtain ⟨w,hw⟩ := (Module.End.hasEigenvalue_of_isRoot hr).exists_hasEigenvector
    exact eigenvalue_ratio_root_of_unity_of_strongFullMatrixSpan ρ hρ hg g hw.2 hv.2
      hw.apply_eq_smul hav)
  let : Uncountable ℂ := Arithmetic.uncountable_complete_normed_field ℂ
  obtain ⟨f'⟩ := Arithmetic.exists_algHom_of_countable (k:=ℚ) (K:=K) (F:=ℂ)
  let f := f'.toRingHom
  let τ := (Matrix.GeneralLinearGroup.map f).comp ρ
  have hτ := hρ.transfer f (RingHom.id ℂ) ρ τ (fun _ _ _ => rfl)
  let E : Matrix n n ℂ ≃ₐ[ℂ] ((n → ℂ) →L[ℂ] (n → ℂ)) :=
    Matrix.toLinAlgEquiv'.trans continuousEndAlgEquiv
  let φ : Matrix n n K →+* ((n → ℂ) →L[ℂ] (n → ℂ)) := E.toRingHom.comp f.mapMatrix
  have hφs (c : K) : φ (c • (1:Matrix n n K))=f c • 1 := by
    have hmat : f.mapMatrix (c • (1:Matrix n n K))=f c • (1:Matrix n n ℂ) := by
      ext i j
      simp only [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_mul]
      congr 1
      exact congrArg (fun M : Matrix n n ℂ => M i j) f.mapMatrix.map_one
    change E (f.mapMatrix (c • (1:Matrix n n K)))=_
    rw [hmat,map_smul,map_one]
  let T := φ (ρ g).val
  have hniM : IsNilpotent ((ρ g).val^m-a^m • (1:Matrix n n K)) := by
    have hh := hni.map (LinearMap.toMatrixAlgEquiv'.toRingHom)
    have hA : LinearMap.toMatrixAlgEquiv' A=(ρ g).val :=
      Matrix.toLinAlgEquiv'.symm_apply_apply _
    change IsNilpotent (LinearMap.toMatrixAlgEquiv' (A^m-a^m • 1)) at hh
    simpa only [map_sub,map_pow,map_smul,map_one,hA] using hh
  have hniT : IsNilpotent (T^m-(f a)^m • 1) := by
    have hh := hniM.map φ
    simpa only [map_sub,map_pow,hφs,T] using hh
  obtain ⟨S,h1,hi,hgen,hgS⟩ := (SparseGrowth.hasPolynomialDegree_iff degree).mp hg
  obtain ⟨δ,hδ,hb⟩ := projective_bound_of_strongFullSpan (matrixRepresentation τ)
    (hτ.strongFullSpan τ) S h1 hgen degree hgS
  have hTpow (k : ℕ) : (continuousRepresentation (matrixRepresentation τ) (g^k)).toContinuousLinearMap=T^k := by
    induction k with
    | zero => ext x i; simp only [pow_zero,map_one]; rfl
    | succ k ih =>
      rw [pow_succ,map_mul,ContinuousLinearEquiv.toContinuousLinearMap_mul,ih,pow_succ]
      rfl
  have hbT (k : ℕ) (x : n → ℂ) : δ*‖T^k‖*‖x‖≤‖(T^k) x‖ := by
    rw [←hTpow]
    exact hb (g^k) x
  let v' : n → ℂ := f ∘ v
  have hv' : v'≠0 := eigenvector_transfer_ne_zero f (RingHom.id ℂ) v v' (fun _ => rfl) hv.2
  have hav' : T v'=f a • v' := eigenvector_transfer f (RingHom.id ℂ)
    (ρ g).val (τ g).val (fun _ _ => rfl) v v' (fun _ => rfl) a (f a) rfl hav
  have hfa : f a≠0 := fun h => ha0 (f.injective (h.trans f.map_zero.symm))
  have hs := scalar_power_of_projective_bound T δ hδ hbT hv' hfa hav' m hniT
  refine ⟨m,hm,a^m,pow_ne_zero m ha0,?_⟩
  have hφinj : Function.Injective φ := by
    intro B C h
    have he := E.injective h
    ext i j
    apply f.injective
    exact congrArg (fun M : Matrix n n ℂ => M i j) he
  apply hφinj
  rw [map_pow,hφs,map_pow]
  exact hs

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_StrongAbstractSpan
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type} [Field K] [CharZero K] [Countable K] [IsAlgClosed K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
variable [Group G] [DecidableEq G]
variable {degree : ℕ}

lemma StrongFullSpan.scalar_power (ρ : G →* (V ≃ₗ[K] V))
    (hρ : StrongFullSpan ρ) (hg : SparseGrowth.HasPolynomialDegree G degree) (g : G) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : K, ((ρ g).toLinearMap)^m=a • (1:End K V) := by
  let b := Module.finBasis K V
  let e := LinearMap.toMatrixAlgEquiv b
  let τ := (linearMatrixEquiv (K:=K) (V:=V)).toMonoidHom.comp ρ
  have hm (g : G) : (τ g).val=e (ρ g).toLinearMap := rfl
  have ht : StrongFullMatrixSpan τ := by
    intro H hH
    let E := e.toLinearEquiv.trans (matrixFlatten (K:=K) (n:=Fin (finrank K V)))
    exact span_equiv_top E (fun h : H => (ρ h.val).toLinearMap) (hρ H hH)
  have : NeZero (finrank K V) := ⟨ne_of_gt (Module.finrank_pos (R:=K) (M:=V))⟩
  obtain ⟨m,hmpos,a,_,ha⟩ := scalar_power_of_strongFullMatrixSpan τ ht hg g
  refine ⟨m,hmpos,a,e.injective ?_⟩
  rw [map_pow,map_smul,map_one,←hm]
  exact ha

lemma StrongFullSpan.virtually_comm_range_bs_oai (ρ : G →* (V ≃ₗ[K] V))
    (hρ : StrongFullSpan ρ) (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∀ x y : (ρ.comp H.subtype).range, x*y=y*x := by
  let := hg.fg
  exact exists_finiteIndex_comm_range_of_projectively_periodic ρ
    (fun g => hρ.scalar_power ρ hg g)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

theorem solution : type_of% @OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range_bs_oai := @OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range_bs_oai
