-- Prove2me | solution 1 for OAI.CriticalPercolation.RelativeGrowth.virtually_indicable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:23:14.303065+00:00
-- url     : https://prove2.me/submissions/ac99c7b9-1145-49f1-8b65-3d5b78d8d3d3

import Mathlib
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_SparseGrowth_HasPolynomialDegree_linear_virtually_indicable

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_NormalClosureGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma eventually_exponential_dominates (C k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, C*n^k < 2^n := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k
    (by norm_num : (1:ℝ)<2)).const_mul (C:ℝ)
  have he : ∀ᶠ n : ℕ in atTop, (C:ℝ)*((n:ℝ)^k / 2^n) < 1 :=
    ht.eventually (Iio_mem_nhds (by simp : (C:ℝ)*0 < 1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hx := hN n hn
  rw [← mul_div_assoc] at hx
  have hx' := (div_lt_one (pow_pos (by norm_num : (0:ℝ)<2) n)).mp hx
  exact_mod_cast hx'

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_RealSparseDoubling
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
    exact_mod_cast (show 0<P by dsimp [P] <;> positivity)
  have hsmall : C*((b*a:ℕ):ℝ)^d<(P:ℝ)*f a :=
    hNF.trans (mul_lt_mul_of_pos_right hNP' hfapos)
  exact (not_lt_of_ge (hlow.trans hupper)) (mul_lt_mul_of_pos_left hsmall hPpos)

lemma exists_local_ratio (f : ℕ → ℝ) (L : ℕ) (hL : 0<L)
    (C : ℝ) (hC : 0<C) (hbound : f L≤C^L*f 0) :
    ∃ i<L, f (i+1)≤C*f i := by
  by_contra! hbad
  have hgrow : ∀ i≤L, C^i*f 0≤f i := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hh := ih (by omega)
      calc
        _ = C*(C^i*f 0) := by rw [pow_succ]; ring
        _ ≤ C*f i := mul_le_mul_of_nonneg_left hh hC.le
        _ ≤ _ := (hbad i (by omega)).le
  have hlast := hbad (L-1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1≤L)] at hlast
  have hg := mul_le_mul_of_nonneg_left (hgrow (L-1) (by omega)) hC.le
  have he : C*(C^(L-1)*f 0)=C^L*f 0 := by
    rw [←mul_assoc,←pow_succ',Nat.sub_add_cancel (by omega : 1≤L)]
  rw [he] at hg
  exact (not_lt_of_ge hbound) (hg.trans_lt hlast)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_PairedSparseScales
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CriticalPercolation.HarmonicAnalysis

lemma coordinate_ratio_bounds (v₀ v₁ d₀ d₁ T : ℝ) (m : ℕ) (hm : 0 < m)
    (hv₀ : 0 < v₀) (hd₀ : 0 < d₀) (hvv : v₀ ≤ v₁) (hdd : d₀ ≤ d₁)
    (hT : 0 ≤ T) (hp : v₁^m*d₁ ≤ T^m*(v₀^m*d₀)) :
    v₁ ≤ T*v₀ ∧ d₁ ≤ T^m*d₀ := by
  have hv₁ := hv₀.trans_le hvv
  have hvm : 0 < v₀^m := pow_pos hv₀ m
  have hvm' := pow_le_pow_left₀ hv₀.le hvv m
  constructor
  · have hlow := mul_le_mul_of_nonneg_left hdd (pow_nonneg hv₁.le m)
    have hp' : v₁^m*d₀ ≤ (T*v₀)^m*d₀ := by
      calc
        _ ≤ _ := hlow
        _ ≤ _ := hp
        _ = _ := by rw [mul_pow]; ring
    have hh := (mul_le_mul_iff_left₀ hd₀).mp hp'
    exact (pow_le_pow_iff_left₀ hv₁.le (mul_nonneg hT hv₀.le) (by omega : m≠0)).mp hh
  · have hlow := mul_le_mul_of_nonneg_right hvm' (hd₀.le.trans hdd)
    apply (mul_le_mul_iff_right₀ hvm).mp
    calc
      _ ≤ _ := hlow
      _ ≤ _ := hp
      _ = _ := by ring

theorem paired_sparse_scales (V D : ℕ → ℝ) (hV : Monotone V) (hD : Monotone D)
    (hVp : ∀ n, 0 < V n) (hDp : ∀ n, 0 < D n)
    (m e : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
    (hpoly : ∀ R, ∃ n ≥ R, (V n)^m*D n ≤ C*(n:ℝ)^(m*e))
    (L : ℕ) (hL : 0 < L) (N : ℕ) :
    ∃ r R : ℕ, N ≤ r ∧ 1 ≤ R ∧ 6*r ≤ R ∧ 10^(2*L)*r ≤ R ∧
      V (7*r) ≤ (10:ℝ)^(4*(e+1))*V r ∧
      D (5*R) ≤ ((10:ℝ)^(4*(e+1)))^m*D R ∧
      V (R+r) ≤ ((10:ℝ)^(4*(e+1)))^L*V r := by
  let F : ℕ → ℝ := fun n => (V n)^m*D n
  have hF : Monotone F := by
    intro n k hnk
    exact mul_le_mul (pow_le_pow_left₀ (hVp n).le (hV hnk) m) (hD hnk)
      (hDp n).le (pow_nonneg (hVp k).le m)
  have hFp : ∀ n ≥ 0, 0 < F n := fun n _ => mul_pos (pow_pos (hVp n) m) (hDp n)
  let b : ℕ := 10^(4*L)
  have hb : 2 ≤ b := by
    have hh : (10:ℕ)^1 ≤ 10^(4*L) := Nat.pow_le_pow_right (by omega) (by omega)
    simpa only [pow_one] using (show 2 ≤ 10 from by omega).trans hh
  obtain ⟨a,ha,haF⟩ := sparse_real_doubling F hF 0 hFp C hC (m*e) b hb hpoly (max N 1)
  have haN : N ≤ a := by omega
  have ha1 : 1 ≤ a := by omega
  let z : ℕ → ℕ := fun i => 10^i*a
  have hzmono : Monotone z := by
    intro i j hij
    exact Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by omega) hij)
  have hz0 : z 0=a := by simp [z]
  have hzsucc (i : ℕ) : z (i+1)=10*z i := by dsimp [z]; rw [pow_succ]; ring
  have hz4 : z (4*L)=b*a := rfl
  let K : ℝ := (10:ℝ)^(4*(e+1))
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hp : (V (z (4*L)))^m*D (z (4*L)) ≤ (K^L)^m*((V a)^m*D a) := by
    dsimp [F] at haF
    apply haF.trans
    have he : (b:ℝ)^(m*(e+1))=(K^L)^m := by
      dsimp [b,K]
      push_cast
      simp only [←pow_mul]
      congr 1
      ring
    rw [←he]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) (by nlinarith : m*e+1 ≤ m*(e+1)))
      (mul_nonneg (pow_nonneg (hVp a).le m) (hDp a).le)
  have haend : a ≤ z (4*L) := by simpa only [hz0] using hzmono (show 0 ≤ 4*L by omega)
  obtain ⟨hvend,hdend⟩ := coordinate_ratio_bounds (V a) (V (z (4*L)))
    (D a) (D (z (4*L))) (K^L) m hm (hVp a) (hDp a)
    (hV haend) (hD haend) (pow_nonneg hK.le L) hp
  have hVblock : V (z L) ≤ K^L*V (z 0) := by
    rw [hz0]
    exact (hV (hzmono (by omega))).trans hvend
  obtain ⟨i,hi,hiratio⟩ := exists_local_ratio (fun j => V (z j)) L hL K hK hVblock
  have hDblock : D (z (3*L+L)) ≤ (K^m)^L*D (z (3*L)) := by
    rw [show 3*L+L=4*L by omega]
    calc
      _ ≤ (K^L)^m*D a := hdend
      _ ≤ (K^L)^m*D (z (3*L)) := mul_le_mul_of_nonneg_left
        (hD (by simpa only [hz0] using hzmono (show 0 ≤ 3*L by omega))) (by positivity)
      _ = _ := by
        have he : (K^L)^m=(K^m)^L := by rw [←pow_mul K,←pow_mul K,Nat.mul_comm L m]
        rw [he]
  obtain ⟨j,hj,hjratio⟩ := exists_local_ratio (fun k => D (z (3*L+k))) L hL (K^m)
    (pow_pos hK m) hDblock
  let r := z i
  let R := z (3*L+j)
  have hsmall : 10^(2*L)*r ≤ R := by
    change 10^(2*L)*(10^i*a) ≤ 10^(3*L+j)*a
    rw [←mul_assoc,←pow_add]
    exact Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by omega) (by omega))
  have hr1 : 1 ≤ r := ha1.trans (by simpa only [hz0] using hzmono (show 0 ≤ i by omega))
  have h6 : 6 ≤ 10^(2*L) := by
    have hh : (10:ℕ)^1 ≤ 10^(2*L) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (by norm_num : 6 ≤ (10:ℕ)^1).trans hh
  have hrR : 6*r ≤ R := (Nat.mul_le_mul_right r h6).trans hsmall
  refine ⟨r,R,haN.trans (by simpa only [hz0] using hzmono (show 0 ≤ i by omega)),by omega,hrR,hsmall,?_,?_,?_⟩
  · apply (hV (show 7*r ≤ z (i+1) by rw [hzsucc]; change 7*r ≤ 10*r; omega)).trans
    exact hiratio
  · have hzlarge : z (3*L+(j+1))=10*R := by rw [show 3*L+(j+1)=(3*L+j)+1 by omega,hzsucc]
    apply (hD (show 5*R ≤ z (3*L+(j+1)) by rw [hzlarge]; omega)).trans
    exact hjratio
  · have hsum : R+r ≤ z (4*L) := by
      apply (show R+r ≤ 10*R by omega).trans
      rw [←hzsucc]
      exact hzmono (by omega)
    calc
      _ ≤ V (z (4*L)) := hV hsum
      _ ≤ K^L*V a := hvend
      _ ≤ K^L*V r := mul_le_mul_of_nonneg_left
        (hV (by simpa only [hz0] using hzmono (show 0 ≤ i by omega))) (by positivity)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteActionAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

lemma sum_smul_orbit (g : G) (x : X) (hf : (MulAction.orbit G x).Finite) (f : X → ℝ) :
    (∑ y∈hf.toFinset, f (g • y))=∑ y∈hf.toFinset, f y := by
  apply Finset.sum_bij (fun y _ => g • y)
  · intro y hy
    apply hf.mem_toFinset.mpr
    obtain ⟨a,rfl⟩ := MulAction.mem_orbit_iff.mp (hf.mem_toFinset.mp hy)
    exact ⟨g*a,mul_smul g a x⟩
  · intro a _ b _ h
    exact MulAction.injective g h
  · intro y hy
    refine ⟨g⁻¹ • y,hf.mem_toFinset.mpr ?_,smul_inv_smul g y⟩
    obtain ⟨a,rfl⟩ := MulAction.mem_orbit_iff.mp (hf.mem_toFinset.mp hy)
    exact ⟨g⁻¹*a,mul_smul g⁻¹ a x⟩
  · intros; rfl

lemma exists_finite_restriction (B : Set X) (hfin : B.Finite)
    (hB : ∀ g : G, ∀ x∈B, g • x∈B) :
    ∃ (H : Type v) (_ : Group H) (_ : Fintype H) (r : H → G),
      (∀ h₁ h₂ x, x∈B → r (h₁*h₂) • x = r h₁ • (r h₂ • x)) ∧
      (∀ g : G, ∃ h : H, ∀ x∈B, r h • x=g • x) := by
  let := hfin.fintype
  let τ := restrictionHom B hB
  let H := τ.range
  let : Fintype H := Fintype.ofFinite H
  let r : H → G := fun h => Classical.choose h.property
  have hr (h : H) : τ (r h)=h.val := Classical.choose_spec h.property
  refine ⟨H,inferInstance,inferInstance,r,?_,?_⟩
  · intro a b x hx
    have he : τ (r (a*b))=τ (r a)*τ (r b) := by rw [hr,hr,hr]; rfl
    exact congrArg (fun e : Equiv.Perm B => (e ⟨x,hx⟩).val) he
  · intro g
    refine ⟨⟨τ g,⟨g,rfl⟩⟩,?_⟩
    intro x hx
    exact congrArg (fun e : Equiv.Perm B => (e ⟨x,hx⟩).val) (hr ⟨τ g,⟨g,rfl⟩⟩)

lemma restricted_orbit_average {H : Type*} [Group H] [Fintype H]
    (B : Set X) (r : H → G)
    (hmul : ∀ a b x, x∈B → r (a*b) • x=r a • (r b • x))
    (hsurj : ∀ g : G, ∃ h : H, ∀ x∈B, r h • x=g • x)
    (x : X) (hx : x∈B) (hf : (MulAction.orbit G x).Finite) (f : X → ℝ) :
    (MulAction.orbit G x).ncard * (∑ h : H, f (r h • x)) =
      (Fintype.card H : ℝ) * ∑ y∈hf.toFinset, f y := by
  have hinv (y : X) (hy : y∈hf.toFinset) :
      (∑ h : H, f (r h • y))=∑ h : H, f (r h • x) := by
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp (hf.mem_toFinset.mp hy)
    obtain ⟨a,ha⟩ := hsurj g
    rw [←ha x hx]
    simp_rw [←hmul _ _ x hx]
    exact Equiv.sum_comp (Equiv.mulRight a) (fun h : H => f (r h • x))
  calc
    _ = ∑ y∈hf.toFinset, ∑ h : H, f (r h • y) := by
      rw [Finset.sum_congr rfl hinv]
      simp only [Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hf]
    _ = ∑ h : H, ∑ y∈hf.toFinset, f (r h • y) := Finset.sum_comm
    _ = _ := by
      simp only [sum_smul_orbit,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteCoverSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {I X : Type*}

lemma finite_incidence_sum (J : Finset I) (L : I → Finset X) (B : Finset X)
    (hsub : ∀ j∈J, L j⊆B) (f : X → ℝ) :
    (∑ j∈J, ∑ x∈L j, f x) =
      ∑ x∈B, ((J.filter (fun j => x∈L j)).card:ℝ)*f x := by
  have he (j : I) (hj : j∈J) : (∑ x∈L j, f x)=∑ x∈B, if x∈L j then f x else 0 := by
    rw [←Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => ⟨hsub j hj hx,hx⟩,fun hx => hx.2⟩
  calc
    _ = ∑ j∈J, ∑ x∈B, if x∈L j then f x else 0 := Finset.sum_congr rfl he
    _ = ∑ x∈B, ∑ j∈J, if x∈L j then f x else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [←Finset.sum_filter]
      simp

lemma sum_le_sum_of_finite_cover (J : Finset I) (L : I → Finset X)
    (F : Finset X) (hcover : ∀ x∈F, ∃ j∈J, x∈L j)
    (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    (∑ x∈F, f x)≤∑ j∈J, ∑ x∈L j, f x := by
  let B := F∪J.biUnion L
  have hJB : ∀ j∈J, L j⊆B := by
    intro j hj x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,hx⟩)
  rw [finite_incidence_sum J L B hJB f]
  calc
    _ ≤ ∑ x∈F, ((J.filter (fun j => x∈L j)).card:ℝ)*f x := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨j,hj,hxj⟩ := hcover x hx
      have hp : 1≤(J.filter (fun j => x∈L j)).card :=
        Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hxj⟩⟩
      have hp' : (1:ℝ)≤(J.filter (fun j => x∈L j)).card := by exact_mod_cast hp
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp' (hf x)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by
      intro x hx hxn
      exact mul_nonneg (Nat.cast_nonneg _) (hf x))

lemma sum_le_sum_of_finite_overlap (J : Finset I) (L : I → Finset X)
    (B : Finset X) (hsub : ∀ j∈J, L j⊆B) (K : ℕ)
    (hover : ∀ x∈B, (J.filter (fun j => x∈L j)).card≤K)
    (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    (∑ j∈J, ∑ x∈L j, f x)≤(K:ℝ)*(∑ x∈B, f x) := by
  rw [finite_incidence_sum J L B hsub f,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hover x hx)) (hf x)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.mem_around
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma reachBall_self (o : X) (r : ℕ) : o∈reachBall Γ o r :=
  ⟨SimpleGraph.Walk.nil,Nat.zero_le _⟩

lemma reachBall_symm {o x : X} {r : ℕ} (h : x∈reachBall Γ o r) :
    o∈reachBall Γ x r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.reverse,by simpa using hp⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma Bounded.mul {S T U : Set A} (hT : Bounded S T) (hU : Bounded S U) : Bounded S (T*U) := by
  obtain ⟨n,hn⟩ := hT; obtain ⟨m,hm⟩ := hU
  exact ⟨n+m,by rw [pow_add]; exact Set.mul_subset_mul hn hm⟩

lemma finite_coset_image_iff_cover (K : Subgroup A) (T : Set A) :
    ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite ↔
      ∃ F : Set A, F.Finite ∧ T⊆F*(K:Set A) := by
  constructor
  · intro hf
    let Q := (QuotientGroup.mk : A → A ⧸ K) '' T
    have hh : ∀ q∈Q, ∃ a∈T, (QuotientGroup.mk a : A ⧸ K)=q := fun q hq => hq
    choose a ha he using hh
    let F := Set.range (fun q : Q => a q.val q.property)
    let : Finite Q := hf.to_subtype
    refine ⟨F,Set.finite_range _,?_⟩
    intro t ht
    let q : Q := ⟨QuotientGroup.mk t,⟨t,ht,rfl⟩⟩
    refine ⟨a q.val q.property,⟨q,rfl⟩,(a q.val q.property)⁻¹*t,?_,by simp⟩
    exact QuotientGroup.eq.mp (he q.val q.property)
  · rintro ⟨F,hF,hcov⟩
    apply (hF.image (QuotientGroup.mk : A → A ⧸ K)).subset
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨f,hf,k,hk,rfl⟩ := hcov ht
    exact ⟨f,hf,QuotientGroup.eq.mpr (by simpa using hk)⟩

lemma HasDegree.bounded_generators {K : Subgroup A} {S T : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hg : HasDegree K S d) (hT : Bounded S T) : HasDegree K T d := by
  obtain ⟨L,hL⟩ := hT
  have hin (n : ℕ) : T^n⊆S^((L+1)*n) := by
    rw [pow_mul]
    exact Set.pow_subset_pow_left (hL.trans (Set.pow_subset_pow_right h1 (Nat.le_succ L)))
  refine ⟨fun n => (hg.1 _).subset (Set.image_mono (hin n)),?_⟩
  obtain ⟨C,hC⟩ := hg.2
  refine ⟨C*(2*(L+1))^d,?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le (by omega : 0<L+1)).mpr (by simpa [Nat.mul_comm] using hr)
  have hnr : (L+1)*n ≤ r := by simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hrn : r≤(2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r (by omega : 0<L+1)
    change r<(L+1)*(n+1) at hlt
    have hh : 1≤n := (le_max_right R 1).trans hn
    nlinarith
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  calc
    _ ≤ (ball K S r).ncard := Set.ncard_le_ncard
      (Set.image_mono ((hin n).trans (Set.pow_subset_pow_right h1 hnr))) (hg.1 r)
    _ ≤ C*r^d := hbound
    _ ≤ C*((2*(L+1))*n)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
    _ = _ := by rw [mul_pow]; ring

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis

namespace Geometry
variable {X : Type*} (W : Geometry X)

lemma self_mem_around (x : X) (r : ℕ) : x∈W.around x r :=
  W.mem_around.mpr (GraphTopology.reachBall_self W.graph x r)
lemma mem_around_symm {x y : X} {r : ℕ} (h : y∈W.around x r) : x∈W.around y r :=
  W.mem_around.mpr (GraphTopology.reachBall_symm W.graph (W.mem_around.mp h))
lemma around_subset_ball {x : X} {R r : ℕ} (hx : x∈W.ball R) : W.around x r⊆W.ball (R+r) :=
  fun _ hy => W.mem_around_add hx hy
lemma ball_card_pos (r : ℕ) : 0<(W.ball r).card :=
  Finset.card_pos.mpr ⟨W.root,W.self_mem_around W.root r⟩

lemma card_around (x : X) (r : ℕ) : (W.around x r).card=(W.ball r).card := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.aut_around_image]
  exact Finset.card_image_of_injective _ g.injective

lemma exists_mem_ball (x : X) : ∃ n, x∈W.ball n := by
  obtain ⟨p,hp,he⟩ := W.connected.exists_path_of_dist W.root x
  exact ⟨p.length,W.mem_around.mpr ⟨p,le_rfl⟩⟩

lemma length_adj {x y : X} (h : W.graph.Adj x y) :
    W.length x≤W.length y+1 ∧ W.length y≤W.length x+1 := by
  have h1 := W.connected.dist_triangle (u:=W.root) (v:=x) (w:=y)
  have h2 := W.connected.dist_triangle (u:=W.root) (v:=y) (w:=x)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at h1
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at h2
  exact ⟨h2,h1⟩

lemma neighbors_card (x : X) : (W.neighbors x).card=(W.neighbors W.root).card := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.neighbors_image]
  exact Finset.card_image_of_injective _ g.injective
lemma energy_nonneg (F : Finset X) (u : X → ℝ) : 0≤W.energy F u := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
lemma energy_mono {F H : Finset X} (h : F⊆H) (u : X → ℝ) : W.energy F u≤W.energy H u := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intros; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma cutoff_nonneg (R : ℕ) (x : X) : 0≤W.cutoff R x := le_max_left _ _
lemma cutoff_large (R : ℕ) {x : X} (hx : x∈W.ball R) : (R:ℝ)≤W.cutoff R x := by
  have hl : (W.length x:ℝ)≤R := by exact_mod_cast W.length_le_iff.mpr hx
  exact (by linarith : (R:ℝ)≤2*R-W.length x).trans (le_max_right _ _)
lemma cutoff_eq_zero (R : ℕ) {x : X} (hx : 2*R≤W.length x) : W.cutoff R x=0 := by
  have hl : 2*(R:ℝ)≤W.length x := by exact_mod_cast hx
  exact max_eq_left (by linarith)
lemma cutoff_ne_zero_length (R : ℕ) {x : X} (hx : W.cutoff R x≠0) : W.length x<2*R := by
  by_contra! h; exact hx (W.cutoff_eq_zero R h)
lemma cutoff_lipschitz (R : ℕ) {x y : X} (h : W.graph.Adj x y) :
    |W.cutoff R y-W.cutoff R x|≤1 := by
  obtain ⟨h1,h2⟩ := W.length_adj h
  have h1' : (W.length x:ℝ)≤(W.length y:ℝ)+1 := by exact_mod_cast h1
  have h2' : (W.length y:ℝ)≤(W.length x:ℝ)+1 := by exact_mod_cast h2
  unfold cutoff
  rw [abs_le]
  constructor <;> rcases le_total 0 (2*(R:ℝ)-W.length y) with hx|hx <;>
    rcases le_total 0 (2*(R:ℝ)-W.length x) with hy|hy <;>
    simp only [max_eq_right hx,max_eq_left hx,max_eq_right hy,max_eq_left hy] <;> linarith

end Geometry
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ActionOrbitTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace ActionOrbitTransport
variable (Λ X : Type*) [Group Λ] [MulAction Λ X]

lemma smul_suborbitCard (φ : Λ) (x y : X) :
    suborbitCard Λ X (φ • x) (φ • y) = suborbitCard Λ X x y := by
  have heq : (fun z => φ • z) '' stabilizerOrbit Λ X x y =
      stabilizerOrbit Λ X (φ • x) (φ • y) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨ψ,hx,hy⟩ := (mem_stabilizerOrbit Λ X).mp hw
      apply (mem_stabilizerOrbit Λ X).mpr
      refine ⟨φ*ψ*φ⁻¹,?_,?_⟩
      · simp only [mul_smul,inv_smul_smul,hx]
      · simp only [mul_smul,inv_smul_smul,hy]
    · intro hz
      obtain ⟨ψ,hx,hy⟩ := (mem_stabilizerOrbit Λ X).mp hz
      refine ⟨φ⁻¹ • z,?_,smul_inv_smul φ z⟩
      apply (mem_stabilizerOrbit Λ X).mpr
      refine ⟨φ⁻¹*ψ*φ,?_,?_⟩
      · simp only [mul_smul,hx,inv_smul_smul]
      · simp only [mul_smul,hy]
  rw [suborbitCard,←heq,Set.ncard_image_of_injective _ (MulAction.injective φ)]
  rfl

end ActionOrbitTransport
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousTransport
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]
open ActionOrbitTransport

lemma reversed_pair_fiber_eq_suborbit (x y : X) :
    {w : X | pairOrbit G X w y=pairOrbit G X x y}=stabilizerOrbit G X y x := by
  ext w
  simp only [Set.mem_ofPred_eq]
  rw [eq_comm,pairOrbit_eq,mem_stabilizerOrbit]
  exact exists_congr (fun g => and_comm)

variable (ht : ∀ x y : X, ∃ g : G, g • x=y)
  (hf : ∀ x y : X, (stabilizerOrbit G X x y).Finite)
  (hu : ∀ x y : X, suborbitCard G X x y=suborbitCard G X y x)

include ht hf in
lemma pair_column_finite (o b y : X) :
    {x : X | pairOrbit G X x y=pairOrbit G X o b}.Finite := by
  obtain ⟨g,rfl⟩ := ht b y
  rw [←smul_pairOrbit G X g o b,reversed_pair_fiber_eq_suborbit]
  exact hf (g • b) (g • o)

include ht hu in
lemma pair_column_card (o b y : X) :
    {x : X | pairOrbit G X x y=pairOrbit G X o b}.ncard=suborbitCard G X o b := by
  obtain ⟨g,rfl⟩ := ht b y
  rw [←smul_pairOrbit G X g o b,reversed_pair_fiber_eq_suborbit]
  change suborbitCard G X (g • b) (g • o)=_
  rw [smul_suborbitCard,hu]

include ht hf hu in
lemma finite_row_sum_bound (o b : X) (F Y : Finset X) (f : X → ℝ)
    (hn : ∀ y∈Y, 0≤f y)
    (hY : ∀ x∈F, ∀ y, pairOrbit G X x y=pairOrbit G X o b → y∈Y) :
    (∑ x∈F, ∑ y∈(pair_row_finite ht hf o b x).toFinset, f y) ≤
      (suborbitCard G X o b : ℝ)*∑ y∈Y, f y := by
  have hr (x : X) (hx : x∈F) :
      ∑ y∈(pair_row_finite ht hf o b x).toFinset, f y=
        ∑ y∈Y, if pairOrbit G X x y=pairOrbit G X o b then f y else 0 := by
    rw [←Finset.sum_filter]
    apply Finset.sum_congr
    · ext y
      simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,Finset.mem_filter]
      exact ⟨fun h => ⟨hY x hx y h,h⟩,And.right⟩
    · intros; rfl
  rw [Finset.sum_congr rfl hr,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hn y hy)
  have hsub : F.filter (fun x => pairOrbit G X x y=pairOrbit G X o b)⊆
      (pair_column_finite ht hf o b y).toFinset := by
    intro x hx
    exact (pair_column_finite ht hf o b y).mem_toFinset.mpr (Finset.mem_filter.mp hx).2
  have hc := Finset.card_le_card hsub
  rw [←Set.ncard_eq_toFinset_card _ (pair_column_finite ht hf o b y), pair_column_card ht hu] at hc
  exact_mod_cast hc

end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

lemma frame_root (x : X) : W.frame x W.root=x := (W.transitive W.root x).choose_spec
lemma frame_smul_root (x : X) : W.frame x • W.root=x := W.frame_root x

lemma suborbit_card_pos (x y : X) : 0 < suborbitCard W.Aut X x y := by
  apply Set.ncard_pos (W.suborbit_finite x y) |>.mpr
  exact ⟨y,(mem_stabilizerOrbit W.Aut X).mpr ⟨1,one_smul _ _,one_smul _ _⟩⟩

lemma stab_ball_preserved (N : ℕ) (k : W.Stab) (x : X) (hx : x∈W.ball N) : k • x∈W.ball N := by
  have hk : k.val W.root=W.root := k.property
  change k.val x∈W.around W.root N
  rw [←hk,←W.aut_around_image]
  exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

lemma row_image (b x : X) :
    (W.suborbit_finite W.root b).toFinset.image (W.frame x)=
      (pair_row_finite W.action_transitive W.suborbit_finite W.root b x).toFinset := by
  ext y
  simp only [Finset.mem_image,Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨k,hk,hz⟩ := (mem_stabilizerOrbit W.Aut X).mp hz
    apply (pairOrbit_eq W.Aut X).mpr
    refine ⟨(W.frame x*k)⁻¹,?_,?_⟩
    · have he : (W.frame x*k) • W.root=x := by
        rw [mul_smul,hk]; exact W.frame_root x
      calc
        _ = (W.frame x*k)⁻¹ • ((W.frame x*k) • W.root) := congrArg _ he.symm
        _ = _ := inv_smul_smul _ _
    · have he : (W.frame x*k) • b=W.frame x z := by rw [mul_smul,hz]; rfl
      rw [←he,inv_smul_smul]
  · intro hy
    obtain ⟨g,hx,hb⟩ := (pairOrbit_eq W.Aut X).mp hy
    refine ⟨(W.frame x)⁻¹ • y,?_,smul_inv_smul (W.frame x) y⟩
    apply (mem_stabilizerOrbit W.Aut X).mpr
    refine ⟨(g*W.frame x)⁻¹,?_,?_⟩
    · have he : (g*W.frame x) • W.root=W.root := by rw [mul_smul,W.frame_smul_root,hx]
      calc
        _ = (g*W.frame x)⁻¹ • ((g*W.frame x) • W.root) := congrArg _ he.symm
        _ = _ := inv_smul_smul _ _
    · rw [mul_inv_rev,mul_smul,←hb,inv_smul_smul]

lemma average_row {H : Type*} [Group H] [Fintype H]
    (N : ℕ) (r : H → W.Stab)
    (hm : ∀ a b x, x∈W.ball N → r (a*b) • x=r a • (r b • x))
    (hs : ∀ k : W.Stab, ∃ h : H, ∀ x∈W.ball N, r h • x=k • x)
    (b : X) (hb : b∈W.ball N) (x : X) (f : X → ℝ) :
    (suborbitCard W.Aut X W.root b : ℝ)*(∑ h : H, f (W.frame x (r h • b)))=
      (Fintype.card H : ℝ)*∑ y∈(pair_row_finite W.action_transitive W.suborbit_finite W.root b x).toFinset, f y := by
  have hh := restricted_orbit_average (G:=W.Stab) (W.ball N : Set X) r hm hs b hb
    (W.suborbit_finite W.root b) (fun z => f (W.frame x z))
  change (suborbitCard W.Aut X W.root b : ℝ)*_= _ at hh
  rw [←W.row_image,Finset.sum_image]
  · exact hh
  · intro a _ b _ he; exact (W.frame x).injective he

lemma average_sum_bound
    (hu : ∀ x y, suborbitCard W.Aut X x y=suborbitCard W.Aut X y x)
    {H : Type*} [Group H] [Fintype H] (N : ℕ) (r : H → W.Stab)
    (hm : ∀ a b x, x∈W.ball N → r (a*b) • x=r a • (r b • x))
    (hs : ∀ k : W.Stab, ∃ h : H, ∀ x∈W.ball N, r h • x=k • x)
    (b : X) (hb : b∈W.ball N) (R : ℕ) (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    (∑ x∈W.ball R, ∑ h : H, f (W.frame x (r h • b)))≤
      (Fintype.card H : ℝ)*∑ y∈W.ball (R+N), f y := by
  have hrow := finite_row_sum_bound W.action_transitive W.suborbit_finite hu W.root b
    (W.ball R) (W.ball (R+N)) f (fun y _ => hf y) (by
      intro x hx y hy
      obtain ⟨g,hgx,hgy⟩ := (pairOrbit_eq W.Aut X).mp hy
      change g x=W.root at hgx
      change g y=b at hgy
      have hyx : y∈W.around x N := by
        have hbx : g y∈W.around (g x) N := by rw [hgx,hgy]; exact hb
        rw [←W.aut_around_image] at hbx
        obtain ⟨z,hz,hze⟩ := Finset.mem_image.mp hbx
        exact (g.injective hze) ▸ hz
      exact W.mem_around_add hx hyx)
  have he : (suborbitCard W.Aut X W.root b : ℝ)*
      (∑ x∈W.ball R, ∑ h : H, f (W.frame x (r h • b)))=
      (Fintype.card H : ℝ)*∑ x∈W.ball R,
        ∑ y∈(pair_row_finite W.action_transitive W.suborbit_finite W.root b x).toFinset, f y := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simpa only [Finset.mul_sum] using W.average_row N r hm hs b hb x f
  have hi := mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg (Fintype.card H))
  rw [←he] at hi
  have hp : (0:ℝ) < suborbitCard W.Aut X W.root b := by exact_mod_cast W.suborbit_card_pos W.root b
  nlinarith

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousGrowth
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.walkFeature_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

lemma not_quadratic_exponential_lower
    (d : ℕ) (hg : W.HasDegree d) (L : ℕ) (hL : 0<L)
    (hlo : ∀ n : ℕ, 2^n ≤ (W.ball (L*n^2)).card) : False := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨N,hN⟩ := SparseGrowth.eventually_exponential_dominates (C*(4*L)^d) (2*d)
  obtain ⟨r,hr,hbound⟩ := hC (L*(max N 1)^2)
  let n := Nat.sqrt (r/L)
  have hn : max N 1 ≤ n := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hL).mpr (by
    simpa only [Nat.mul_comm] using hr))
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : L*n^2 ≤ r := by
    calc
      _ ≤ L*(r/L) := Nat.mul_le_mul_left L (Nat.sqrt_le' (r/L))
      _ ≤ r := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self r L
  have hrn : r ≤ (4*L)*n^2 := by
    have ht := Nat.lt_mul_div_succ r hL
    have hs : r/L+1 ≤ (n+1)^2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' (r/L))
    have hs' : (n+1)^2 ≤ 4*n^2 := by nlinarith
    have hj := (Nat.mul_le_mul_left L hs).trans (Nat.mul_le_mul_left L hs')
    nlinarith
  have hu : 2^n ≤ (C*(4*L)^d)*n^(2*d) := by
    calc
      _ ≤ (W.ball (L*n^2)).card := hlo n
      _ ≤ (W.ball r).card := Finset.card_le_card (W.ball_mono hnr)
      _ ≤ C*r^d := hbound
      _ ≤ C*((4*L)*n^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
      _ = (C*(4*L)^d)*n^(2*d) := by rw [mul_pow,pow_mul]; ring
  exact (not_le_of_gt (hN n ((le_max_left N 1).trans hn))) hu

lemma suborbit_card_relIndex (x y : X) : suborbitCard W.Aut X x y=
    (MulAction.stabilizer W.Aut y).relIndex (MulAction.stabilizer W.Aut x) := by
  have he : (MulAction.stabilizer W.Aut y).subgroupOf (MulAction.stabilizer W.Aut x)=
      MulAction.stabilizer (MulAction.stabilizer W.Aut x) y := by ext g; rfl
  rw [Subgroup.relIndex,he,MulAction.index_stabilizer]
  rfl

lemma ratio_relativeMass (x y : X) : W.ratio x y=
    Subgroup.relativeMass (MulAction.stabilizer W.Aut x) (MulAction.stabilizer W.Aut y) := by
  simp only [ratio,W.suborbit_card_relIndex,Subgroup.relativeMass]
lemma ratio_cocycle (x y z : X) : W.ratio x y*W.ratio y z=W.ratio x z := by
  simp only [W.ratio_relativeMass]
  apply Subgroup.relativeMass_cocycle
  all_goals
    rw [←W.suborbit_card_relIndex]
    exact ne_of_gt (W.suborbit_card_pos _ _)
lemma ratio_self (x : X) : W.ratio x x=1 := by
  rw [W.ratio_relativeMass,Subgroup.relativeMass_self]
lemma ratio_aut (g : W.Aut) (x y : X) : W.ratio (g x) (g y)=W.ratio x y := by
  change W.ratio (g • x) (g • y)=_
  simp only [ratio,smul_suborbitCard]
lemma ratio_pow (g : W.Aut) (x : X) (n : ℕ) : W.ratio x ((g^n) x)=(W.ratio x (g x))^n := by
  induction n with
  | zero => change W.ratio x x=(W.ratio x (g x))^0; rw [W.ratio_self,pow_zero]
  | succ n ih =>
    have he : (g^(n+1)) x=(g^n) (g x) := by rw [pow_succ]; rfl
    rw [he,←W.ratio_cocycle x ((g^n) x),W.ratio_aut,ih,pow_succ]

lemma aut_pow_ball (g : W.Aut) (x : X) (L : ℕ) (hl : g x∈W.around x L) (n : ℕ) :
    (g^n) x∈W.around x (n*L) := by
  induction n with
  | zero => change x∈W.around x (0*L); simpa only [Nat.zero_mul] using W.self_mem_around x 0
  | succ n ih =>
    have hstep : (g^n) (g x)∈W.around ((g^n) x) L := by
      rw [←W.aut_around_image]
      exact Finset.mem_image.mpr ⟨g x,hl,rfl⟩
    have hh := W.mem_around_add ih hstep
    have he : (g^(n+1)) x=(g^n) (g x) := by rw [pow_succ]; rfl
    simpa only [Nat.add_mul,Nat.one_mul,←he] using hh

lemma ratio_power_card_bound (g : W.Aut) (x : X) (L : ℕ) (hl : g x∈W.around x L) (n : ℕ) :
    (W.ratio x (g x))^n≤((W.ball (n*L)).card:ℝ) := by
  rw [←W.ratio_pow]
  have hr : W.ratio x ((g^n) x)≤(suborbitCard W.Aut X x ((g^n) x):ℝ) := by
    apply div_le_self (Nat.cast_nonneg _)
    exact_mod_cast W.suborbit_card_pos ((g^n) x) x
  apply hr.trans
  have hsub : stabilizerOrbit W.Aut X x ((g^n) x)⊆(W.around x (n*L):Set X) := by
    intro y hy
    obtain ⟨k,hk,rfl⟩ := (mem_stabilizerOrbit W.Aut X).mp hy
    change k x=x at hk
    change k ((g^n) x)∈W.around x (n*L)
    simpa only [hk] using W.mem_around.mpr
      (GraphTopology.iso_reachBall W.graph k (W.mem_around.mp (W.aut_pow_ball g x L hl n)))
  have hc := Set.ncard_le_ncard hsub (W.around x (n*L)).finite_toSet
  rw [Set.ncard_coe_finset,W.card_around x (n*L)] at hc
  exact_mod_cast hc

lemma ratio_le_one (d : ℕ) (hg : W.HasDegree d) (x y : X) : W.ratio x y≤1 := by
  by_contra! hr
  obtain ⟨g,hgxy⟩ := W.transitive x y
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (2:ℝ) hr
  let a := g^k
  have ha : 2≤W.ratio x (a x) := by
    dsimp [a]
    rw [W.ratio_pow,hgxy]
    exact hk.le
  obtain ⟨p,_,_⟩ := W.connected.exists_path_of_dist x (a x)
  let L := max p.length 1
  have him : a x∈W.around x L := W.mem_around.mpr ⟨p,le_max_left _ _⟩
  apply W.not_quadratic_exponential_lower d hg L (lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))
  intro n
  have hb := W.ratio_power_card_bound a x L him n
  have he : (2:ℝ)^n≤((W.ball (n*L)).card:ℝ) :=
    (pow_le_pow_left₀ (by norm_num) ha n).trans hb
  have hh : 2^n≤(W.ball (n*L)).card := by exact_mod_cast he
  apply hh.trans (Finset.card_le_card (W.ball_mono ?_))
  have hn : n≤n^2 := by nlinarith
  nlinarith

theorem balanced_suborbits (d : ℕ) (hg : W.HasDegree d) (x y : X) :
    suborbitCard W.Aut X x y=suborbitCard W.Aut X y x := by
  have h1 := W.ratio_le_one d hg x y
  have h2 := W.ratio_le_one d hg y x
  have hp : (0:ℝ) < suborbitCard W.Aut X y x := by exact_mod_cast W.suborbit_card_pos y x
  have hq : (0:ℝ) < suborbitCard W.Aut X x y := by exact_mod_cast W.suborbit_card_pos x y
  dsimp [ratio] at h1 h2
  have he : (suborbitCard W.Aut X x y:ℝ)=(suborbitCard W.Aut X y x:ℝ) := by
    apply le_antisymm
    · exact (div_le_one hp).mp h1
    · exact (div_le_one hq).mp h2
  exact_mod_cast he

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

namespace Presentation
variable (P : Presentation A)

lemma walk_endpoint {x y : P.X} (p : P.graph.Walk x y) :
    ∀ g : A, P.projection g=x → ∃ h∈P.S^p.length, P.projection (g*h)=y := by
  induction p with
  | nil => intro g hg; exact ⟨1,by simp,by simpa using hg⟩
  | @cons x y z h p ih =>
    intro g hg
    obtain ⟨_,s,hs,he⟩ := (P.adj_mk_iff g y).mp (hg ▸ h)
    obtain ⟨t,ht,hz⟩ := ih (g*s) he
    refine ⟨s*t,?_,?_⟩
    · rw [SimpleGraph.Walk.length_cons,pow_succ']
      exact Set.mul_mem_mul hs ht
    · simpa only [mul_assoc] using hz
lemma reachBall_subset (n : ℕ) : GraphTopology.reachBall P.graph P.root n⊆ball P.K P.S n := by
  rintro y ⟨p,hp⟩
  obtain ⟨h,hh,he⟩ := P.walk_endpoint p 1 rfl
  exact ⟨h,Set.pow_subset_pow_right P.one_mem hp hh,by simpa using he⟩
lemma geometry_hasDegree (d : ℕ) (hg : HasDegree P.K P.S d) :
    (P.geometry (hg.1 1)).HasDegree d := by
  obtain ⟨hf,C,hC⟩ := hg
  refine ⟨C,?_⟩
  intro R
  obtain ⟨n,hn,hbound⟩ := hC R
  refine ⟨n,hn,?_⟩
  have hs : ((P.geometry (hf 1)).ball n : Set P.X)⊆ball P.K P.S n := by
    intro y hy
    exact P.reachBall_subset n ((P.geometry (hf 1)).mem_around.mp hy)
  have hc := Set.ncard_le_ncard hs (hf n)
  rw [Set.ncard_coe_finset] at hc
  exact hc.trans hbound

end Presentation
end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma finite_image_of_finite_coset_image {B : Type*} [Group B]
    (K : Subgroup A) (f : A →* B) (hK : (f '' (K:Set A)).Finite)
    (T : Set A) (hT : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    (f '' T).Finite := by
  obtain ⟨F,hF,hcov⟩ := (finite_coset_image_iff_cover K T).mp hT
  apply ((hF.image f).mul hK).subset
  rintro _ ⟨t,ht,rfl⟩
  obtain ⟨a,ha,k,hk,rfl⟩ := hcov ht
  rw [map_mul]
  exact Set.mul_mem_mul ⟨a,ha,rfl⟩ ⟨k,hk,rfl⟩

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetImageGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma exists_finite_coset_cover (K : Subgroup A) (T : Set A)
    (hf : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    ∃ F : Set A, F.Finite ∧ F.ncard=((QuotientGroup.mk : A → A ⧸ K) '' T).ncard ∧ T⊆F*(K:Set A) := by
  let Q := (QuotientGroup.mk : A → A ⧸ K) '' T
  have hh : ∀ q∈Q, ∃ a∈T, (QuotientGroup.mk a : A ⧸ K)=q := fun q hq => hq
  choose a ha he using hh
  let F := Set.range (fun q : Q => a q.val q.property)
  let : Finite Q := hf.to_subtype
  have hi : Injective (fun q : Q => a q.val q.property) := by
    intro q r h
    apply Subtype.ext
    rw [←he q.val q.property,←he r.val r.property]
    exact congrArg (QuotientGroup.mk : A → A ⧸ K) h
  refine ⟨F,Set.finite_range _,?_,?_⟩
  · rw [Set.ncard_range_of_injective hi]
    rfl
  · intro t ht
    let q : Q := ⟨QuotientGroup.mk t,⟨t,ht,rfl⟩⟩
    refine ⟨a q.val q.property,⟨q,rfl⟩,(a q.val q.property)⁻¹*t,?_,by simp⟩
    exact QuotientGroup.eq.mp (he q.val q.property)

lemma image_ncard_bound (K : Subgroup A) (f : A →* B) (hK : (f '' (K:Set A)).Finite)
    (T : Set A) (hT : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    (f '' T).ncard≤((QuotientGroup.mk : A → A ⧸ K) '' T).ncard*(f '' (K:Set A)).ncard := by
  obtain ⟨F,hF,hFc,hcov⟩ := exists_finite_coset_cover K T hT
  have hs : f '' T⊆(f '' F)*(f '' (K:Set A)) := by
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨a,ha,k,hk,rfl⟩ := hcov ht
    rw [map_mul]
    exact Set.mul_mem_mul ⟨a,ha,rfl⟩ ⟨k,hk,rfl⟩
  calc
    _ ≤ ((f '' F)*(f '' (K:Set A))).ncard := Set.ncard_le_ncard hs ((hF.image f).mul hK)
    _ ≤ (f '' F).ncard*(f '' (K:Set A)).ncard := by
      have hh := @Finset.card_mul_le B _ _ (hF.image f).toFinset hK.toFinset
      simpa only [←Set.ncard_coe_finset,Finset.coe_mul,Set.Finite.coe_toFinset] using hh
    _ ≤ F.ncard*(f '' (K:Set A)).ncard := Nat.mul_le_mul_right _ (Set.ncard_image_le hF)
    _ = _ := by rw [hFc]

lemma HasDegree.image_polynomial {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤) (hg : HasDegree K S d)
    (f : A →* B) (hf : Surjective f) (hK : (f '' (K:Set A)).Finite) :
    SparseGrowth.HasPolynomialDegree B d := by
  have hSf : (f '' S).Finite := finite_image_of_finite_coset_image K f hK S (by simpa only [ball,pow_one] using hg.1 1)
  refine ⟨f '' S,hSf,⟨1,h1,map_one f⟩,?_,?_,?_,?_⟩
  · rw [←Set.image_inv,hi]
  · rw [←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective f hf
  · exact hg.2.choose*(f '' (K:Set A)).ncard
  · intro R
    obtain ⟨n,hn,hb⟩ := hg.2.choose_spec R
    refine ⟨n,hn,?_⟩
    rw [←Set.image_pow]
    calc
      _ ≤ (ball K S n).ncard*(f '' (K:Set A)).ncard := image_ncard_bound K f hK (S^n) (hg.1 n)
      _ ≤ (hg.2.choose*n^d)*(f '' (K:Set A)).ncard := Nat.mul_le_mul_right _ hb
      _ = _ := by ring

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma normalized_generators (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) :
    ∃ P : Presentation A, P.K=K ∧ Bounded S P.S ∧ S⊆P.S := by
  let T := (K:Set A)*S*(K:Set A)
  have hs : S⊆T := by
    intro s hs
    have hh := Set.mul_mem_mul (Set.mul_mem_mul K.one_mem hs) K.one_mem
    simpa only [one_mul,mul_one] using hh
  have hT1 : (1:A)∈T := hs h1
  have hTi : T⁻¹=T := by
    dsimp [T]
    rw [mul_inv_rev,mul_inv_rev,inv_coe_set,hi,mul_assoc]
  have hTgen : Subgroup.closure T=⊤ := top_unique (hgen ▸ Subgroup.closure_mono hs)
  have hleft : (K:Set A)*T⊆T := by
    rintro _ ⟨k,hk,_,⟨_,⟨l,hl,s,hs,rfl⟩,m,hm,rfl⟩,rfl⟩
    have hh := Set.mul_mem_mul (Set.mul_mem_mul (K.mul_mem hk hl) hs) hm
    simpa only [T,mul_assoc] using hh
  refine ⟨⟨K,T,hT1,hTi,hTgen,hleft⟩,rfl,?_,hs⟩
  exact (hK.mul ⟨1,by simp⟩).mul hK

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousBallPacking
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.walkFeature_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
variable {X : Type*} (W : Geometry X)

lemma packing_card_bound (J : Finset X) (r : ℕ)
    (hJ : (J:Set X).PairwiseDisjoint (fun a => W.around a r))
    (F : Finset X) (hF : ∀ a∈J, W.around a r⊆F) :
    J.card*(W.ball r).card≤F.card := by
  calc
    _ = ∑ a∈J, (W.around a r).card := by simp only [W.card_around,Finset.sum_const_nat]
    _ = (J.biUnion (fun a => W.around a r)).card := (Finset.card_biUnion hJ).symm
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      obtain ⟨a,ha,hx⟩ := Finset.mem_biUnion.mp hx
      exact hF a ha hx)

theorem exists_word_ball_packing (R r : ℕ) :
    ∃ J : Finset X, J⊆W.ball R ∧
      (J:Set X).PairwiseDisjoint (fun a => W.around a r) ∧
      J.card*(W.ball r).card≤(W.ball (R+r)).card ∧
      ∀ x∈W.ball R, ∃ a∈J, x∈W.around a (2*r) := by
  let C : Finset (Finset X) := (W.ball R).powerset.filter
    (fun (J : Finset X) => (J:Set X).PairwiseDisjoint (fun a => W.around a r))
  obtain ⟨J,hJmax⟩ := C.exists_maximal <| Finset.filter_nonempty_iff.mpr
    ⟨∅,Finset.empty_mem_powerset _,by simp⟩
  simp only [C,Finset.mem_filter,Finset.mem_powerset] at hJmax
  obtain ⟨hJR,hJ⟩ := hJmax.1
  refine ⟨J,hJR,hJ,W.packing_card_bound J r hJ _ (fun a ha => W.around_subset_ball (hJR ha)),?_⟩
  intro x hx
  by_cases hxJ : x∈J
  · exact ⟨x,hxJ,W.self_mem_around _ _⟩
  by_cases! hd : ∀ a∈J, Disjoint (W.around x r) (W.around a r)
  · exact False.elim (hJmax.not_gt
      ⟨Finset.insert_subset_iff.mpr ⟨hx,hJR⟩,by
        rw [Finset.coe_insert]
        exact hJ.insert (fun a ha _ => hd a ha)⟩
      (Finset.ssubset_insert hxJ))
  · obtain ⟨a,ha,hd⟩ := hd
    obtain ⟨y,hyx,hya⟩ := Finset.not_disjoint_iff.mp hd
    refine ⟨a,ha,?_⟩
    simpa only [show r+r=2*r by omega] using W.mem_around_add hya (W.mem_around_symm hyx)

lemma packing_overlap (J : Finset X) (r t K : ℕ)
    (hJ : (J:Set X).PairwiseDisjoint (fun a => W.around a r))
    (hvol : (W.ball (t+r)).card≤K*(W.ball r).card) (x : X) :
    (J.filter (fun a => x∈W.around a t)).card≤K := by
  let I := J.filter (fun a => x∈W.around a t)
  have hIJ : I⊆J := Finset.filter_subset _ _
  have hId : (I:Set X).PairwiseDisjoint (fun a => W.around a r) := fun a ha b hb hab => hJ (hIJ ha) (hIJ hb) hab
  have hsub (a : X) (ha : a∈I) : W.around a r⊆W.around x (t+r) := by
    intro y hy
    exact W.mem_around_add (W.mem_around_symm (Finset.mem_filter.mp ha).2) hy
  have hh := W.packing_card_bound I r hId (W.around x (t+r)) hsub
  rw [W.card_around x (t+r)] at hh
  exact le_of_mul_le_mul_right (hh.trans hvol) (W.ball_card_pos r)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_CayleyPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A] [DecidableEq A]

omit [Group A] [DecidableEq A] in
lemma finite_variance_identity (F : Finset A) (u : A → ℝ) :
    (∑ x∈F, ∑ y∈F, (u x-u y)^2) =
      2*(F.card:ℝ)*(∑ x∈F, (u x)^2)-2*(∑ x∈F, u x)^2 := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,←Finset.sum_mul,←Finset.mul_sum,nsmul_eq_mul]
  ring

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_HarmonicFunctionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {X : Type*}

lemma vanishingSubspace_antitone (D : Submodule ℝ (X → ℝ)) :
    Antitone (vanishingSubspace D) := by
  intro s t h u hu x hx
  exact hu x (h hx)

theorem exists_detecting_ball (F : ℕ → Set X) (hmono : Monotone F)
    (hex : ∀ x, ∃ n, x∈F n) (D : Submodule ℝ (X → ℝ))
    [FiniteDimensional ℝ D] :
    ∃ n, ∀ u : D, (∀ x∈F n, (u:X → ℝ) x=0) → u=0 := by
  let K : ℕ →o (Submodule ℝ D)ᵒᵈ :=
    ⟨fun n => vanishingSubspace D (F n),
      fun m n h => vanishingSubspace_antitone D (hmono h)⟩
  obtain ⟨n,hn⟩ := IsArtinian.monotone_stabilizes K
  refine ⟨n,?_⟩
  intro u hu
  apply Subtype.ext
  funext x
  obtain ⟨m,hm⟩ := hex x
  have he : vanishingSubspace D (F n)=vanishingSubspace D (F (max n m)) :=
    hn (max n m) (le_max_left _ _)
  have hum : u∈vanishingSubspace D (F (max n m)) := he ▸ hu
  exact hum x (hmono (le_max_right _ _) hm)

lemma squareMass_nonneg (F : Finset X) (u : X → ℝ) : 0≤ squareMass F u :=
  Finset.sum_nonneg (fun vertex _ => sq_nonneg (u vertex))

lemma squareMass_eq_zero_iff (F : Finset X) (u : X → ℝ) :
    squareMass F u=0 ↔ ∀ x∈F, u x=0 := by
  rw [squareMass,Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (u x))]
  simp only [sq_eq_zero_iff]

lemma squareMass_mono {F H : Finset X} (h : F⊆H) (u : X → ℝ) :
    squareMass F u≤ squareMass H u :=
  Finset.sum_le_sum_of_subset_of_nonneg h (by intros; positivity)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_HarmonicEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {V : Type*} [Fintype V]

lemma finite_green_identity (w : V → V → ℝ) (hw : ∀ x y, w x y=w y x)
    (u v : V → ℝ) :
    (∑ x, ∑ y, w x y*(u x-u y)*(v x-v y)) =
      2*∑ x, v x*(∑ y, w x y*(u x-u y)) := by
  have hs : (∑ x, ∑ y, w x y*(u x-u y)*v y) =
      -(∑ x, ∑ y, w x y*(u x-u y)*v x) := by
    rw [Finset.sum_comm,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [hw x y]
    ring
  have hsplit : (∑ x, ∑ y, w x y*(u x-u y)*(v x-v y)) =
      (∑ x, ∑ y, w x y*(u x-u y)*v x) -
      (∑ x, ∑ y, w x y*(u x-u y)*v y) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsplit,hs]
  have he : (∑ x, ∑ y, w x y*(u x-u y)*v x) =
      (∑ x, v x*(∑ y, w x y*(u x-u y))) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he]
  ring

lemma finite_cutoff_energy_identity (w : V → V → ℝ)
    (hw : ∀ x y, w x y=w y x) (u η : V → ℝ)
    (hh : ∀ x, η x=0 ∨ (∑ y, w x y*(u x-u y))=0) :
    (∑ x, ∑ y, w x y*(η x*u x-η y*u y)^2) =
      (∑ x, ∑ y, w x y*(u x*u y)*(η x-η y)^2) := by
  have hg := finite_green_identity w hw u (fun x => η x^2*u x)
  have hz : (∑ x, ∑ y, w x y*(u x-u y)*(η x^2*u x-η y^2*u y))=0 := by
    rw [hg]
    have hs : (∑ x, (η x^2*u x)*(∑ y, w x y*(u x-u y)))=0 := by
      apply Finset.sum_eq_zero
      intro x _
      rcases hh x with h | h <;> simp [h]
    rw [hs,mul_zero]
  have he : (∑ x, ∑ y, w x y*(u x-u y)*(η x^2*u x-η y^2*u y)) =
      (∑ x, ∑ y, w x y*(η x*u x-η y*u y)^2) -
      (∑ x, ∑ y, w x y*(u x*u y)*(η x-η y)^2) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  exact sub_eq_zero.mp (he.symm.trans hz)

theorem finite_caccioppoli (w : V → V → ℝ)
    (hw : ∀ x y, w x y=w y x) (hw0 : ∀ x y, 0≤w x y)
    (u η : V → ℝ)
    (hh : ∀ x, η x=0 ∨ (∑ y, w x y*(u x-u y))=0) :
    (∑ x, ∑ y, w x y*(η x)^2*(u x-u y)^2) ≤
      4*(∑ x, ∑ y, w x y*(u x)^2*(η x-η y)^2) := by
  let E := ∑ x, ∑ y, w x y*(η x*u x-η y*u y)^2
  let B := ∑ x, ∑ y, w x y*(u x)^2*(η x-η y)^2
  have hswap : (∑ x, ∑ y, w x y*(u y)^2*(η x-η y)^2)=B := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    rw [hw x y]
    ring
  have hE : 2*E≤2*B := by
    rw [show E=(∑ x, ∑ y, w x y*(u x*u y)*(η x-η y)^2) from
      finite_cutoff_energy_identity w hw u η hh]
    have hb : 2*B=B+(∑ x, ∑ y, w x y*(u y)^2*(η x-η y)^2) := by rw [hswap]; ring
    rw [hb]
    unfold B
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    have hhxy := mul_nonneg (hw0 x y) (sq_nonneg (u x-u y))
    have hhxy' := mul_nonneg hhxy (sq_nonneg (η x-η y))
    nlinarith
  have hgrad : (∑ x, ∑ y, w x y*(η x)^2*(u x-u y)^2) ≤
      2*E+2*(∑ x, ∑ y, w x y*(u y)^2*(η x-η y)^2) := by
    unfold E
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    have hsq := mul_nonneg (hw0 x y)
      (sq_nonneg ((η x*u x-η y*u y)+(u y*(η x-η y))))
    nlinarith
  rw [hswap] at hgrad
  change _≤4*B
  linarith

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_CayleyCaccioppoli
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

omit [Group A] in
lemma sum_subtype_pair (F : Finset A) (f : A → A → ℝ) :
    (∑ x:F, ∑ y:F, f x.val y.val)=∑ x∈F, ∑ y∈F, f x y := by
  simp only [Finset.sum_coe_sort]
  exact Finset.sum_coe_sort F (fun x => ∑ y∈F, f x y)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_HomogeneousCaccioppoli
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.walkFeature_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma sum_neighbor_rows (F : Finset X) (x : X) (f : X → ℝ)
    (hF : ∀ y∈W.neighbors x, y∈F) :
    (∑ y∈F, if W.graph.Adj x y then f y else 0)=∑ y∈W.neighbors x, f y := by
  rw [←Finset.sum_filter]
  apply Finset.sum_congr
  · ext y
    simp only [Finset.mem_filter,W.mem_neighbors]
    exact ⟨And.right,fun h => ⟨hF y (W.mem_neighbors.mpr h),h⟩⟩
  · intros; rfl

lemma sum_neighbor_rows_le (F : Finset X) (x : X) (f : X → ℝ)
    (hf : ∀ y, 0≤f y) :
    (∑ y∈F, if W.graph.Adj x y then f y else 0)≤∑ y∈W.neighbors x, f y := by
  rw [←Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy; exact W.mem_neighbors.mpr (Finset.mem_filter.mp hy).2
  · intros; apply hf

lemma cutoff_neighbor_mem_ball (R : ℕ) {x : X} (hx : W.cutoff R x≠0)
    {y : X} (hy : y∈W.neighbors x) : y∈W.ball (2*R+1) := by
  apply W.length_le_iff.mp
  have hl := W.cutoff_ne_zero_length R hx
  have hh := (W.length_adj (W.mem_neighbors.mp hy)).2
  omega

theorem caccioppoli (u : X → ℝ) (hu : W.IsHarmonic u) (R : ℕ) :
    (R:ℝ)^2*W.energy (W.ball R) u ≤
      4*(W.degree:ℝ)*squareMass (W.ball (2*R+1)) u := by
  let F := W.ball (2*R+1)
  let w : F → F → ℝ := fun x y => if W.graph.Adj x.val y.val then 1 else 0
  let η : F → ℝ := fun x => W.cutoff R x.val
  have hw (x y : F) : w x y=w y x := by
    dsimp [w]
    exact if_congr (W.graph.adj_comm _ _) rfl rfl
  have hw0 (x y : F) : 0≤w x y := by dsimp [w]; split <;> positivity
  have hh (x : F) : η x=0 ∨ (∑ y:F, w x y*(u x.val-u y.val))=0 := by
    by_cases hx : η x=0
    · exact Or.inl hx
    right
    have hx' : W.cutoff R x.val≠0 := hx
    simp only [w,ite_mul,one_mul,zero_mul]
    rw [Finset.sum_coe_sort F (fun y : X =>
      if W.graph.Adj x.val y then u x.val-u y else 0)]
    rw [W.sum_neighbor_rows F x.val (fun y => u x.val-u y)
      (fun s hs => W.cutoff_neighbor_mem_ball R hx' hs)]
    exact hu x.val
  have hc := finite_caccioppoli w hw hw0 (fun x:F => u x.val) η hh
  have hL : (R:ℝ)^2*W.energy (W.ball R) u ≤
      ∑ x:F, ∑ y:F, w x y*(η x)^2*(u x.val-u y.val)^2 := by
    simp only [w,η,ite_mul,one_mul,zero_mul]
    rw [show (∑ x:F, ∑ y:F, if W.graph.Adj x.val y.val then
      (W.cutoff R x.val)^2*(u x.val-u y.val)^2 else 0) =
      ∑ x∈F, ∑ y∈F, if W.graph.Adj x y then
      (W.cutoff R x)^2*(u x-u y)^2 else 0 from
      sum_subtype_pair F (fun x y => if W.graph.Adj x y then
        (W.cutoff R x)^2*(u x-u y)^2 else 0)]
    have hsub : W.ball R⊆F := W.ball_mono (by omega)
    calc
      _ = ∑ x∈W.ball R, (R:ℝ)^2*(∑ y∈W.neighbors x, (u x-u y)^2) := by
        unfold energy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ ≤ ∑ x∈W.ball R, (W.cutoff R x)^2*(∑ y∈W.neighbors x, (u x-u y)^2) := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_right
        · exact sq_le_sq₀ (by positivity) (W.cutoff_nonneg R x) |>.mpr (W.cutoff_large R hx)
        · exact Finset.sum_nonneg (fun s _ => sq_nonneg _)
      _ = ∑ x∈W.ball R, ∑ y∈F,
          if W.graph.Adj x y then (W.cutoff R x)^2*(u x-u y)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [W.sum_neighbor_rows]
        · exact Finset.mul_sum _ _ _
        · intro y hy
          apply W.length_le_iff.mp
          have hlx := W.length_le_iff.mpr hx
          have hhx := (W.length_adj (W.mem_neighbors.mp hy)).2
          omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro x hx hxn
        exact Finset.sum_nonneg (fun y hy => by split <;> positivity))
  have hU : (∑ x:F, ∑ y:F, w x y*(u x.val)^2*(η x-η y)^2) ≤
      (W.degree:ℝ)*squareMass F u := by
    simp only [w,η,ite_mul,one_mul,zero_mul]
    rw [show (∑ x:F, ∑ y:F, if W.graph.Adj x.val y.val then
      (u x.val)^2*(W.cutoff R x.val-W.cutoff R y.val)^2 else 0) =
      ∑ x∈F, ∑ y∈F, if W.graph.Adj x y then
      (u x)^2*(W.cutoff R x-W.cutoff R y)^2 else 0 from
      sum_subtype_pair F (fun x y => if W.graph.Adj x y then
        (u x)^2*(W.cutoff R x-W.cutoff R y)^2 else 0)]
    unfold squareMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    calc
      _ ≤ ∑ y∈F, if W.graph.Adj x y then (u x)^2 else 0 := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hs : W.graph.Adj x y
        · simp only [ite_eq_left hs]
          have ha := W.cutoff_lipschitz R hs
          rw [abs_sub_comm] at ha
          have hsquare := (sq_le_one_iff_abs_le_one _).mpr ha
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hsquare (sq_nonneg (u x))
        · simp only [ite_eq_right hs,le_refl]
      _ ≤ ∑ y∈W.neighbors x, (u x)^2 := W.sum_neighbor_rows_le _ _ _ (by intro y; positivity)
      _ = _ := by simp [W.neighbors_card]
  have hU' := mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤4)
  change _≤4*(W.degree:ℝ)*squareMass F u
  calc
    _ ≤ _ := hL.trans hc
    _ ≤ _ := by simpa only [mul_assoc] using hU'

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_HomogeneousPoincare
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

lemma getVert_mem_ball {b : X} (p : W.graph.Walk W.root b) (N i : ℕ) (hp : p.length≤N) :
    p.getVert i∈W.ball N := by
  apply W.mem_around.mpr
  exact ⟨p.take i,(p.take_length i).le.trans (min_le_right _ _) |>.trans hp⟩

lemma walk_square_bound {a b : X} (p : W.graph.Walk a b) (f : X → ℝ) :
    (f b-f a)^2≤(p.length:ℝ)*∑ i∈Finset.range p.length, (f (p.getVert (i+1))-f (p.getVert i))^2 := by
  have hh := sq_sum_le_card_mul_sum_sq (s:=Finset.range p.length)
    (f:=fun i => f (p.getVert (i+1))-f (p.getVert i))
  rw [Finset.sum_range_sub (fun i => f (p.getVert i)),Finset.card_range,p.getVert_zero,p.getVert_length] at hh
  exact hh

lemma averaged_path_bound
    (hu : ∀ x y, suborbitCard W.Aut X x y=suborbitCard W.Aut X y x)
    {H : Type*} [Group H] [Fintype H] (N : ℕ) (r : H → W.Stab)
    (hm : ∀ a b x, x∈W.ball N → r (a*b) • x=r a • (r b • x))
    (hs : ∀ k : W.Stab, ∃ h : H, ∀ x∈W.ball N, r h • x=k • x)
    (b : X) (p : W.graph.Walk W.root b) (hp : p.length≤N) (R : ℕ) (u : X → ℝ) :
    (∑ x∈W.ball R, ∑ h : H, (u (W.frame x (r h • b))-u x)^2)≤
      (N:ℝ)^2*(Fintype.card H : ℝ)*W.energy (W.ball (R+N)) u := by
  let e : X → ℝ := fun y => ∑ z∈W.neighbors y, (u z-u y)^2
  have he (y : X) : 0≤e y := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hg (i : ℕ) (hi : i∈Finset.range p.length) :
      (∑ x∈W.ball R, ∑ h : H,
        (u (W.frame x (r h • p.getVert (i+1)))-u (W.frame x (r h • p.getVert i)))^2)≤
        (Fintype.card H : ℝ)*W.energy (W.ball (R+N)) u := by
    have hav := W.average_sum_bound hu N r hm hs (p.getVert i) (W.getVert_mem_ball p N i hp) R e he
    apply le_trans _ hav
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro h hh
    have hadj := (W.frame x).map_adj_iff.mpr ((r h).val.map_adj_iff.mpr (p.adj_getVert_succ (Finset.mem_range.mp hi)))
    exact Finset.single_le_sum (f:=fun z => (u z-u (W.frame x (r h • p.getVert i)))^2)
      (fun _ _ => sq_nonneg _) (W.mem_neighbors.mpr hadj)
  have hb (x : X) (h : H) := W.walk_square_bound p (fun z => u (W.frame x (r h • z)))
  have hb' (x : X) (h : H) :
      (u (W.frame x (r h • b))-u x)^2≤(p.length:ℝ)*
        ∑ i∈Finset.range p.length,
          (u (W.frame x (r h • p.getVert (i+1)))-u (W.frame x (r h • p.getVert i)))^2 := by
    have hk : r h • W.root=W.root := (r h).property
    simpa only [hk,W.frame_root] using hb x h
  have hsum := Finset.sum_le_sum (fun x (_ : x∈W.ball R) =>
    Finset.sum_le_sum (fun h (_ : h∈Finset.univ) => hb' x h))
  simp only [←Finset.mul_sum] at hsum
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.range p.length)] at hsum
  rw [Finset.sum_comm (s:=W.ball R) (t:=Finset.range p.length)] at hsum
  have hgrad := Finset.sum_le_sum hg
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hgrad
  have hn : (p.length:ℝ)≤N := by exact_mod_cast hp
  have hnn : (0:ℝ)≤p.length := Nat.cast_nonneg _
  have hNn : (0:ℝ)≤N := Nat.cast_nonneg _
  have hc : (0:ℝ)≤Fintype.card H := Nat.cast_nonneg _
  have hE := W.energy_nonneg (W.ball (R+N)) u
  have hh := mul_le_mul_of_nonneg_left hgrad hnn
  have hsquare := (sq_le_sq₀ hnn hNn).mpr hn
  have hh' := mul_le_mul_of_nonneg_right hsquare (mul_nonneg hc hE)
  nlinarith

lemma pair_sum_le_aut (u : X → ℝ) (r : ℕ) (x : X) (hx : x∈W.ball r)
    (a : W.Aut) (ha : a W.root=x) :
    (∑ y∈W.ball r, (u y-u x)^2)≤∑ b∈W.ball (2*r), (u (a b)-u x)^2 := by
  have hsub : W.ball r⊆W.around x (2*r) := by
    intro y hy
    simpa only [show r+r=2*r by omega] using W.mem_around_add (W.mem_around_symm hx) hy
  calc
    _ ≤ ∑ y∈W.around x (2*r), (u y-u x)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = _ := by
      rw [←ha,←W.aut_around_image,Finset.sum_image]
      intro b _ c _ he; exact a.injective he

theorem ball_poincare
    (hun : ∀ x y, suborbitCard W.Aut X x y=suborbitCard W.Aut X y x)
    (u : X → ℝ) (r : ℕ) (hu : (∑ x∈W.ball r, u x)=0) :
    (W.ball r).card*(∑ x∈W.ball r, (u x)^2)≤
      2*(r:ℝ)^2*((W.ball (2*r)).card:ℝ)*W.energy (W.ball (3*r)) u := by
  obtain ⟨H,hH,hHF,t,htm,hts⟩ := exists_finite_restriction (G:=W.Stab)
    (W.ball (2*r):Set X) (W.ball (2*r)).finite_toSet (W.stab_ball_preserved (2*r))
  let := hH
  let := hHF
  have hav (b : X) (hb : b∈W.ball (2*r)) :
      (∑ x∈W.ball r, ∑ h : H, (u (W.frame x (t h • b))-u x)^2)≤
        (2*(r:ℝ))^2*(Fintype.card H:ℝ)*W.energy (W.ball (3*r)) u := by
    obtain ⟨p,hp⟩ := W.mem_around.mp hb
    simpa only [show r+2*r=3*r by omega,Nat.cast_mul,Nat.cast_ofNat] using
      W.averaged_path_bound hun (2*r) t htm hts b p hp r u
  have hlower (x : X) (hx : x∈W.ball r) (h : H) :
      (∑ y∈W.ball r, (u y-u x)^2)≤∑ b∈W.ball (2*r), (u (W.frame x (t h • b))-u x)^2 := by
    apply W.pair_sum_le_aut u r x hx (W.frame x*(t h).val)
    change W.frame x ((t h).val W.root)=x
    rw [show (t h).val W.root=W.root from (t h).property,W.frame_root]
  have hl := Finset.sum_le_sum (fun x (hx : x∈W.ball r) =>
    Finset.sum_le_sum (fun h (_ : h∈Finset.univ) => hlower x hx h))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum] at hl
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=W.ball (2*r))] at hl
  rw [Finset.sum_comm (s:=W.ball r) (t:=W.ball (2*r))] at hl
  have hs := Finset.sum_le_sum hav
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hid := HarmonicAnalysis.finite_variance_identity (W.ball r) u
  have hswap : (∑ x∈W.ball r, ∑ y∈W.ball r, (u y-u x)^2)=
      2*((W.ball r).card:ℝ)*(∑ x∈W.ball r, (u x)^2) := by
    rw [Finset.sum_comm,hid,hu]; ring
  rw [hswap] at hl
  have hpos : (0:ℝ)<Fintype.card H := by exact_mod_cast Fintype.card_pos
  nlinarith [hl.trans hs]

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousCover
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis ActionOrbitTransport

variable {A : Type*} (W : Geometry A)

lemma squareMass_around (a : A) (r : ℕ) (u : A → ℝ) :
    squareMass (W.around a r) u=squareMass (W.ball r) (fun x => u (W.frame a x)) := by
  unfold squareMass
  have him : W.around a r=(W.ball r).image (W.frame a) := by
    rw [W.aut_around_image,W.frame_root]
  rw [him]
  rw [Finset.sum_image]
  intro x _ y _ h
  exact (W.frame a).injective h

lemma sum_around (a : A) (r : ℕ) (u : A → ℝ) :
    (∑ x∈W.around a r, u x)=∑ y∈W.ball r, u (W.frame a y) := by
  have him : W.around a r=(W.ball r).image (W.frame a) := by
    rw [W.aut_around_image,W.frame_root]
  rw [him]
  rw [Finset.sum_image]
  intro x _ y _ h
  exact (W.frame a).injective h

lemma energy_around (a : A) (r : ℕ) (u : A → ℝ) :
    W.energy (W.around a r) u=W.energy (W.ball r) (fun x => u (W.frame a x)) := by
  unfold energy
  have him : W.around a r=(W.ball r).image (W.frame a) := by
    rw [W.aut_around_image,W.frame_root]
  rw [him,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [←W.neighbors_image,Finset.sum_image]
    intro x _ y _ h; exact (W.frame a).injective h
  · intro x _ y _ h; exact (W.frame a).injective h

variable (hun : ∀ x y, suborbitCard W.Aut A x y=suborbitCard W.Aut A y x)
include hun

lemma translated_poincare (a : A) (r K : ℕ) (u : A → ℝ)
    (hvol : (W.ball (7*r)).card≤K*(W.ball r).card)
    (hu : (∑ x∈W.around a (2*r), u x)=0) :
    squareMass (W.around a (2*r)) u ≤
      8*(r:ℝ)^2*(K:ℝ)*W.energy (W.around a (6*r)) u := by
  rw [W.sum_around] at hu
  have hp := W.ball_poincare hun
    (fun x => u (W.frame a x)) (2*r) hu
  change ((W.ball (2*r)).card:ℝ)*squareMass (W.ball (2*r)) (fun x => u (W.frame a x)) ≤ _ at hp
  rw [←W.squareMass_around] at hp
  have he : W.energy (W.ball (3*(2*r))) (fun x => u (W.frame a x)) =
      W.energy (W.around a (6*r)) u := by
    rw [W.energy_around a (6*r) u]
    rw [show 3*(2*r)=6*r by omega]
  rw [he] at hp
  have hv : (W.ball (2*(2*r))).card≤K*(W.ball (2*r)).card := by
    calc
      _ ≤ (W.ball (7*r)).card := Finset.card_le_card (W.ball_mono (by omega))
      _ ≤ _ := hvol.trans (Nat.mul_le_mul_left _ (Finset.card_le_card (W.ball_mono (by omega))))
  have hv' : ((W.ball (2*(2*r))).card:ℝ)≤(K:ℝ)*((W.ball (2*r)).card:ℝ) := by exact_mod_cast hv
  have hbpos : (0:ℝ)<(W.ball (2*r)).card := by exact_mod_cast W.ball_card_pos (2*r)
  have hepos := W.energy_nonneg (W.around a (6*r)) u
  have hm := mul_le_mul_of_nonneg_right hv' (mul_nonneg (sq_nonneg (r:ℝ)) hepos)
  push_cast at hp
  nlinarith

lemma cover_mass_energy (R r K : ℕ) (J : Finset A)
    (hJR : J⊆W.ball R)
    (hJ : (J:Set A).PairwiseDisjoint (fun a => W.around a r))
    (hcover : ∀ x∈W.ball R, ∃ a∈J, x∈W.around a (2*r))
    (hvol : (W.ball (7*r)).card≤K*(W.ball r).card)
    (u : A → ℝ) (hu : ∀ a∈J, (∑ x∈W.around a (2*r), u x)=0) :
    squareMass (W.ball R) u ≤
      8*(r:ℝ)^2*(K:ℝ)^2*W.energy (W.ball (R+6*r)) u := by
  have hcover' := sum_le_sum_of_finite_cover J (fun a => W.around a (2*r))
    (W.ball R) hcover (fun x => (u x)^2) (fun x => sq_nonneg _)
  have hpsum := Finset.sum_le_sum (fun a (ha : a∈J) => W.translated_poincare hun a r K u hvol (hu a ha))
  have hsub : ∀ a∈J, W.around a (6*r)⊆W.ball (R+6*r) :=
    fun a ha => W.around_subset_ball (hJR ha)
  have hover : ∀ x∈W.ball (R+6*r), (J.filter (fun a => x∈W.around a (6*r))).card≤K := by
    intro x _
    apply W.packing_overlap J r (6*r) K hJ
    simpa only [show 6*r+r=7*r by omega] using hvol
  have he := sum_le_sum_of_finite_overlap J (fun a => W.around a (6*r))
    (W.ball (R+6*r)) hsub K hover
    (fun x => ∑ y∈W.neighbors x, (u y-u x)^2)
    (fun x => Finset.sum_nonneg (fun s _ => sq_nonneg _))
  change (∑ a∈J, W.energy (W.around a (6*r)) u)≤
    (K:ℝ)*W.energy (W.ball (R+6*r)) u at he
  simp only [←Finset.mul_sum] at hpsum
  change squareMass (W.ball R) u≤∑ a∈J, squareMass (W.around a (2*r)) u at hcover'
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0≤8*(r:ℝ)^2*(K:ℝ))
  calc
    _ ≤ _ := hcover'.trans hpsum
    _ ≤ _ := by nlinarith

theorem harmonic_cover_kernel_bound (R r K : ℕ) (hR : 1≤R) (hrR : 6*r≤R)
    (J : Finset A) (hJR : J⊆W.ball R)
    (hJ : (J:Set A).PairwiseDisjoint (fun a => W.around a r))
    (hcover : ∀ x∈W.ball R, ∃ a∈J, x∈W.around a (2*r))
    (hvol : (W.ball (7*r)).card≤K*(W.ball r).card)
    (u : A → ℝ) (hharm : W.IsHarmonic u)
    (hu : ∀ a∈J, (∑ x∈W.around a (2*r), u x)=0) :
    (R:ℝ)^2*squareMass (W.ball R) u ≤
      8*(K:ℝ)^2*(W.degree:ℝ)*(r:ℝ)^2*squareMass (W.ball (5*R)) u := by
  have hp := W.cover_mass_energy hun R r K J hJR hJ hcover hvol u hu
  have hem := W.energy_mono (W.ball_mono (show R+6*r≤2*R by omega)) u
  have hm := mul_le_mul_of_nonneg_left hem (by positivity : 0≤8*(r:ℝ)^2*(K:ℝ)^2)
  have hp' : squareMass (W.ball R) u≤8*(r:ℝ)^2*(K:ℝ)^2*W.energy (W.ball (2*R)) u := hp.trans hm
  have hc := W.caccioppoli u hharm (2*R)
  have hqm := squareMass_mono (W.ball_mono (show 2*(2*R)+1≤5*R by omega)) u
  have hq := mul_le_mul_of_nonneg_left hqm (by positivity : 0≤4*(W.degree:ℝ))
  have hc' : (R:ℝ)^2*W.energy (W.ball (2*R)) u≤
      (W.degree:ℝ)*squareMass (W.ball (5*R)) u := by
    push_cast at hc
    nlinarith
  have hm' := mul_le_mul_of_nonneg_left hp' (sq_nonneg (R:ℝ))
  have hm'' := mul_le_mul_of_nonneg_left hc' (by positivity : 0≤8*(r:ℝ)^2*(K:ℝ)^2)
  nlinarith

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousPolynomialSpace
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.walkFeature_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
variable {A : Type*} (W : Geometry A)

lemma finite_family_growth_bound {ι : Type*} [Fintype ι] (k : ℕ) (v : ι → A → ℝ)
    (hv : ∀ i, W.HasPolynomialGrowth k (v i)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, 1 ≤ n → ∀ i, ∀ x∈W.ball n,
      |v i x| ≤ M*(n:ℝ)^k := by
  choose C hC hCv using hv
  let M := (∑ i, C i)*2^k
  have hm0 : 0 ≤ M := mul_nonneg (Finset.sum_nonneg (fun i _ => hC i)) (by positivity)
  refine ⟨M,hm0,?_⟩
  intro n hn i x hx
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hCi : C i ≤ ∑ j, C j := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  calc
    _ ≤ C i*((n:ℝ)+1)^k := hCv i n x hx
    _ ≤ (∑ j, C j)*((n:ℝ)+1)^k := mul_le_mul_of_nonneg_right hCi (by positivity)
    _ ≤ (∑ j, C j)*(2*(n:ℝ))^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) k) (Finset.sum_nonneg (fun j _ => hC j))
    _ = M*(n:ℝ)^k := by dsimp [M]; rw [mul_pow]; ring

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GeneralizedGramSpectrum
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix InnerProductSpace

namespace CriticalPercolation.HarmonicAnalysis
variable {ι : Type*} [Fintype ι]

lemma hermitian_dot_comm (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ M *ᵥ y = y ⬝ᵥ M *ᵥ x := by
  have ht : Mᵀ=M := Matrix.isHermitian_iff_isSymm.mp hM
  calc
    _ = Matrix.vecMul x M ⬝ᵥ y := Matrix.dotProduct_mulVec x M y
    _ = Matrix.vecMul x Mᵀ ⬝ᵥ y := by rw [ht]
    _ = _ := by rw [Matrix.vecMul_transpose,dotProduct_comm]

theorem generalized_gram_spectrum (A B : Matrix ι ι ℝ) (hA : A.PosDef)
    (hB : B.IsHermitian) (hmono : ∀ x, matrixQuadratic A x≤ matrixQuadratic B x) :
    ∃ (μ : Fin (Fintype.card ι) → ℝ) (b : Module.Basis (Fin (Fintype.card ι)) ℝ (ι → ℝ)),
      (∀ i, 1≤μ i) ∧ B.det=A.det*(∏ i, μ i) ∧
      (∀ x, matrixQuadratic A x=∑ i, (b.repr x i)^2) ∧
      (∀ x, matrixQuadratic B x=∑ i, μ i*(b.repr x i)^2) := by
  let := A.toNormedAddCommGroup hA
  let : SeminormedAddCommGroup (ι → ℝ) := (A.toNormedAddCommGroup hA).toSeminormedAddCommGroup
  let := A.toInnerProductSpace hA.posSemidef
  let T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := Matrix.toLin' (A⁻¹*B)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hinner (x y : ι → ℝ) : ⟪x,y⟫_ℝ=x ⬝ᵥ A *ᵥ y := by
    change (A *ᵥ y) ⬝ᵥ star x = _
    simp only [star_trivial,dotProduct_comm]
  have hTinner (x y : ι → ℝ) : ⟪x,T y⟫_ℝ=x ⬝ᵥ B *ᵥ y := by
    rw [hinner]
    change x ⬝ᵥ A *ᵥ ((A⁻¹*B) *ᵥ y)=_
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv_cancel_left A B hdet]
  have hT : LinearMap.IsSymmetric (𝕜 := ℝ) (E := ι → ℝ) T := by
    intro x y
    rw [real_inner_comm y (T x),hTinner,hTinner]
    exact hermitian_dot_comm B hB y x
  have hn : Module.finrank ℝ (ι → ℝ)=Fintype.card ι := Module.finrank_fintype_fun_eq_card ℝ
  let b := hT.eigenvectorBasis hn
  let μ := hT.eigenvalues hn
  have hQa (x : ι → ℝ) : matrixQuadratic A x=⟪x,x⟫_ℝ := (hinner x x).symm
  have hQb (x : ι → ℝ) : matrixQuadratic B x=⟪x,T x⟫_ℝ := (hTinner x x).symm
  have hμ (i : Fin (Fintype.card ι)) : 1≤μ i := by
    have hh := hmono (b i)
    rw [hQa,hQb,hT.apply_eigenvectorBasis hn i,inner_smul_right] at hh
    change ⟪b i,b i⟫_ℝ ≤ μ i*⟪b i,b i⟫_ℝ at hh
    simpa only [real_inner_self_eq_norm_sq,OrthonormalBasis.norm_eq_one,one_pow,mul_one] using hh
  refine ⟨μ,b.toBasis,hμ,?_,?_,?_⟩
  · have hh := hT.det_eq_prod_eigenvalues hn
    change (Matrix.toLin' (A⁻¹*B)).det=∏ i, μ i at hh
    rw [LinearMap.det_toLin',Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv] at hh
    calc
      B.det = A.det*(A.det⁻¹*B.det) := by field_simp [hA.det_pos.ne']
      _ = _ := congrArg (A.det*·) hh
  · intro x
    rw [hQa,←b.sum_inner_mul_inner x x]
    apply Finset.sum_congr rfl
    intro i _
    rw [b.coe_toBasis_repr_apply,b.repr_apply_apply,real_inner_comm x (b i)]
    ring
  · intro x
    rw [hQb,←b.sum_inner_mul_inner x (T x)]
    apply Finset.sum_congr rfl
    intro i _
    rw [b.coe_toBasis_repr_apply,b.repr_apply_apply,←hT (b i) x,
      hT.apply_eigenvectorBasis hn i,inner_smul_left,real_inner_comm x (b i)]
    change ⟪x,b i⟫_ℝ * (μ i*⟪x,b i⟫_ℝ) = μ i*⟪x,b i⟫_ℝ^2
    ring

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_FunctionGramMatrix
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis
variable {ι X : Type*} [Fintype ι]

omit [Fintype ι] in
lemma functionGram_hermitian (F : Finset X) (v : ι → X → ℝ) :
    (functionGram F v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial,functionGram,mul_comm]

lemma functionGram_quadratic (F : Finset X) (v : ι → X → ℝ) (a : ι → ℝ) :
    matrixQuadratic (functionGram F v) a = squareMass F (functionCombination v a) := by
  simp only [matrixQuadratic,functionGram,Matrix.mulVec,dotProduct,
    squareMass,functionCombination,pow_two,Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ i, ∑ x∈F, ∑ j, a i*(v i x*v j x*a j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ x∈F, ∑ i, ∑ j, a i*(v i x*v j x*a j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma functionGram_posDef (F : Finset X) (v : ι → X → ℝ)
    (hdetect : ∀ a, (∀ x∈F, functionCombination v a x=0) → a=0) :
    (functionGram F v).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨functionGram_hermitian F v,?_⟩
  intro a ha
  simp only [star_trivial]
  change 0 < matrixQuadratic (functionGram F v) a
  rw [functionGram_quadratic]
  apply lt_of_le_of_ne (squareMass_nonneg _ _)
  intro hz
  exact ha (hdetect a ((squareMass_eq_zero_iff _ _).mp hz.symm))

lemma functionGram_quadratic_mono {F H : Finset X} (hFH : F⊆H)
    (v : ι → X → ℝ) (a : ι → ℝ) :
    matrixQuadratic (functionGram F v) a ≤ matrixQuadratic (functionGram H v) a := by
  rw [functionGram_quadratic,functionGram_quadratic]
  exact squareMass_mono hFH _

lemma functionGram_det_mono {F H : Finset X} (hFH : F⊆H)
    (v : ι → X → ℝ) (hF : (functionGram F v).PosDef) :
    (functionGram F v).det ≤ (functionGram H v).det := by
  obtain ⟨μ,b,hμ,hdet,_,_⟩ := generalized_gram_spectrum
    (functionGram F v) (functionGram H v) hF (functionGram_hermitian H v)
    (functionGram_quadratic_mono hFH v)
  rw [hdet]
  have hp : (1:ℝ) ≤ ∏ i, μ i := Finset.one_le_prod (fun index _ => hμ index)
  exact le_mul_of_one_le_right hF.det_pos.le hp

omit [Fintype ι] in
lemma functionGram_entry_bound (F : Finset X) (v : ι → X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hv : ∀ i, ∀ x∈F, |v i x| ≤ M) (i j : ι) :
    |functionGram F v i j| ≤ (F.card:ℝ)*M^2 := by
  calc
    _ ≤ ∑ x∈F, |v i x*v j x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x∈F, M^2 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul,pow_two]
      exact mul_le_mul (hv i x hx) (hv j x hx) (abs_nonneg _) hM
    _ = _ := by simp

lemma functionGram_det_bound (F : Finset X) (v : ι → X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hv : ∀ i, ∀ x∈F, |v i x| ≤ M) :
    |(functionGram F v).det| ≤ ((Fintype.card ι).factorial:ℝ)*((F.card:ℝ)*M^2)^(Fintype.card ι) := by
  have hh := Matrix.det_le (abv := AbsoluteValue.abs) (functionGram_entry_bound F v M hM hv)
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using hh

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GramGrowthScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis
variable {A ι : Type*} [Group A] [Fintype ι]

omit [Group A] in
lemma functionCombination_eq_linearCombination (v : ι → A → ℝ) (a : ι → ℝ) :
    functionCombination v a = Fintype.linearCombination ℝ v a := by
  funext x
  simp only [functionCombination,Fintype.linearCombination_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_HomogeneousGramScales
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.walkFeature_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix

namespace CriticalPercolation.HomogeneousAnalysis
open HarmonicAnalysis

variable {A ι : Type*} [Fintype ι]

namespace Geometry
variable (W : Geometry A)

lemma exists_posDef_functionGram (v : ι → A → ℝ) (hv : LinearIndependent ℝ v) :
    ∃ n₀ : ℕ, ∀ n≥n₀, (functionGram (W.ball n) v).PosDef := by
  let f := Fintype.linearCombination ℝ v
  obtain ⟨n₀,hn₀⟩ := exists_detecting_ball (fun n => (W.ball n:Set A))
    (fun i j h => W.ball_mono h) W.exists_mem_ball f.range
  refine ⟨n₀,?_⟩
  intro n hn
  apply functionGram_posDef
  intro a ha
  have hzero : f a=0 := by
    have hh := hn₀ ⟨f a,⟨a,rfl⟩⟩ (fun x hx => by
      change f a x=0
      rw [←functionCombination_eq_linearCombination]
      exact ha x (W.ball_mono hn hx))
    exact congrArg Subtype.val hh
  exact hv.fintypeLinearCombination_injective (by simpa only [map_zero] using hzero)

lemma gram_sparse_product_growth (d k : ℕ) (hg : W.HasDegree d)
    (v : ι → A → ℝ) (hv : ∀ i, W.HasPolynomialGrowth k (v i)) (n₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R, ∃ n≥R,
      ((W.ball (max n n₀)).card:ℝ)^(Fintype.card ι) *
          (functionGram (W.ball (max n n₀)) v).det ≤
        C*(n:ℝ)^((Fintype.card ι)*(2*d+2*k)) := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨M,hM,hvM⟩ := W.finite_family_growth_bound k v hv
  let m := Fintype.card ι
  let D : ℝ := (m.factorial:ℝ)*((C:ℝ)*M^2)^m
  refine ⟨(C:ℝ)^m*D,by dsimp [D] <;> positivity,?_⟩
  intro R
  obtain ⟨n,hn,hvn⟩ := hC (max R (max n₀ 1))
  have hnR : R ≤ n := by omega
  have hn₀ : n₀ ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hvol : ((W.ball n).card:ℝ) ≤ (C:ℝ)*(n:ℝ)^d := by exact_mod_cast hvn
  have hbase : ((W.ball n).card:ℝ)*(M*(n:ℝ)^k)^2 ≤
      ((C:ℝ)*M^2)*(n:ℝ)^(d+2*k) := by
    calc
      _ ≤ ((C:ℝ)*(n:ℝ)^d)*(M*(n:ℝ)^k)^2 :=
        mul_le_mul_of_nonneg_right hvol (sq_nonneg _)
      _ = _ := by rw [mul_pow,←pow_mul,pow_add]; ring_nf
  have hdet : (functionGram (W.ball n) v).det ≤ D*(n:ℝ)^(m*(d+2*k)) := by
    calc
      _ ≤ |(functionGram (W.ball n) v).det| := le_abs_self _
      _ ≤ (m.factorial:ℝ)*(((W.ball n).card:ℝ)*(M*(n:ℝ)^k)^2)^m :=
        functionGram_det_bound _ _ _ (mul_nonneg hM (by positivity)) (hvM n hn1)
      _ ≤ (m.factorial:ℝ)*(((C:ℝ)*M^2)*(n:ℝ)^(d+2*k))^m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase m) (by positivity)
      _ = _ := by
        rw [mul_pow,←pow_mul (n:ℝ),Nat.mul_comm (d+2*k) m]
        dsimp [D]
        ring
  refine ⟨n,hnR,?_⟩
  rw [max_eq_left hn₀]
  calc
    _ ≤ ((W.ball n).card:ℝ)^m*(D*(n:ℝ)^(m*(d+2*k))) :=
      mul_le_mul_of_nonneg_left hdet (by positivity)
    _ ≤ ((C:ℝ)*(n:ℝ)^d)^m*(D*(n:ℝ)^(m*(d+2*k))) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hvol m)
        (by dsimp [D] <;> positivity)
    _ = _ := by
      rw [mul_pow,←pow_mul]
      calc
        _ = ((C:ℝ)^m*D)*((n:ℝ)^(d*m)*(n:ℝ)^(m*(d+2*k))) := by ring
        _ = _ := by rw [←pow_add]; congr 2; ring

theorem function_gram_paired_scales (d k : ℕ) (hg : W.HasDegree d)
    (v : ι → A → ℝ) (hv : ∀ i, W.HasPolynomialGrowth k (v i))
    (hli : LinearIndependent ℝ v) (hm : 0 < Fintype.card ι)
    (L : ℕ) (hL : 0 < L) (N : ℕ) :
    ∃ r R : ℕ, N ≤ r ∧ 1 ≤ R ∧ 6*r ≤ R ∧ 10^(2*L)*r ≤ R ∧
      (W.ball (7*r)).card ≤ 10^(4*(2*d+2*k+1))*(W.ball r).card ∧
      (functionGram (W.ball (5*R)) v).det ≤
        ((10:ℝ)^(4*(2*d+2*k+1)))^(Fintype.card ι)*(functionGram (W.ball R) v).det ∧
      (W.ball (R+r)).card ≤ (10^(4*(2*d+2*k+1)))^L*(W.ball r).card ∧
      (functionGram (W.ball R) v).PosDef := by
  obtain ⟨n₀,hn₀⟩ := W.exists_posDef_functionGram v hli
  let V : ℕ → ℝ := fun n => (W.ball (max n n₀)).card
  let D : ℕ → ℝ := fun n => (functionGram (W.ball (max n n₀)) v).det
  have hV : Monotone V := by
    intro i j hij
    dsimp [V]
    exact_mod_cast Finset.card_le_card (W.ball_mono (max_le_max hij (le_refl n₀)))
  have hD : Monotone D := by
    intro i j hij
    exact functionGram_det_mono (W.ball_mono (max_le_max hij le_rfl)) v
      (hn₀ _ (le_max_right _ _))
  have hVp : ∀ n, 0 < V n := by intro n; dsimp [V]; exact_mod_cast W.ball_card_pos (max n n₀)
  have hDp : ∀ n, 0 < D n := fun n => (hn₀ _ (le_max_right _ _)).det_pos
  obtain ⟨C,hC,hpoly⟩ := W.gram_sparse_product_growth d k hg v hv n₀
  obtain ⟨r,R,hr,hR,hrR,hscale,hvr,hdr,hvR⟩ := paired_sparse_scales V D hV hD hVp hDp
    (Fintype.card ι) (2*d+2*k) hm C hC hpoly L hL (max N n₀)
  have hr₀ : n₀ ≤ r := by omega
  have hR₀ : n₀ ≤ R := by omega
  simp only [V,D,max_eq_left hr₀,max_eq_left hR₀,
    max_eq_left (show n₀ ≤ 7*r by omega),max_eq_left (show n₀ ≤ 5*R by omega),
    max_eq_left (show n₀ ≤ R+r by omega)] at hvr hdr hvR
  refine ⟨r,R,by omega,hR,hrR,hscale,?_,hdr,?_,hn₀ R hR₀⟩
  · exact_mod_cast hvr
  · exact_mod_cast hvR

end Geometry
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_MatrixLowGrowthSubspace
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis
variable {ι : Type*} [Fintype ι]

lemma many_small_factors (μ : ι → ℝ) (hμ : ∀ i, 1 ≤ μ i)
    (C : ℝ) (hC : 1 < C) (hprod : (∏ i, μ i) ≤ C^(Fintype.card ι)) :
    Fintype.card ι ≤ 2*(Finset.univ.filter (fun i => μ i ≤ C^2)).card := by
  let I := Finset.univ.filter (fun i => μ i ≤ C^2)
  let J := Finset.univ.filter (fun i => C^2 < μ i)
  have hj (i : ι) : (if i∈J then C^2 else 1) ≤ μ i := by
    split_ifs with hi
    · exact (Finset.mem_filter.mp hi).2.le
    · exact hμ i
  have hp := Finset.prod_le_prod (fun i (_ : i∈Finset.univ) => by
      split_ifs <;> positivity) (fun i (_ : i∈Finset.univ) => hj i)
  have he : (∏ i : ι, if i∈J then C^2 else 1)=(C^2)^J.card := by
    rw [←Finset.prod_filter]
    simp
  rw [he,←pow_mul] at hp
  have hcard : 2*J.card ≤ Fintype.card ι := (pow_le_pow_iff_right₀ hC).mp (hp.trans hprod)
  have hIJ : I.card+J.card=Fintype.card ι := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => μ i ≤ C^2)
    simpa only [not_le,Finset.card_univ] using hh
  change Fintype.card ι ≤ 2*I.card
  omega

omit [Fintype ι] in
lemma basis_support_span {E : Type*} [AddCommGroup E] [Module ℝ E] (b : Basis ι ℝ E) (I : Finset ι)
    {x : E} (hx : x∈Submodule.span ℝ (Set.range (fun i:I => b i.val))) :
    ∀ i∉I, b.repr x i=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    intro i hi
    have hj : j.val≠i := by intro he; exact hi (he ▸ j.property)
    simp [hj]
  | zero => simp
  | add x y hx hy ix iy =>
    intro i hi
    simp only [map_add,Finsupp.add_apply,ix i hi,iy i hi,add_zero]
  | smul a x hx ix =>
    intro i hi
    simp only [map_smul,Finsupp.smul_apply,smul_eq_mul,ix i hi,mul_zero]

theorem exists_low_growth_subspace (A B : Matrix ι ι ℝ) (hA : A.PosDef)
    (hB : B.IsHermitian) (hmono : ∀ x, matrixQuadratic A x ≤ matrixQuadratic B x)
    (C : ℝ) (hC : 1 < C) (hdet : B.det ≤ C^(Fintype.card ι)*A.det) :
    ∃ V : Submodule ℝ (ι → ℝ),
      Fintype.card ι ≤ 2*Module.finrank ℝ V ∧
      ∀ x∈V, matrixQuadratic B x ≤ C^2*matrixQuadratic A x := by
  obtain ⟨μ,b,hμ,hd,hqa,hqb⟩ := generalized_gram_spectrum A B hA hB hmono
  have hp : (∏ i, μ i) ≤ C^(Fintype.card ι) := by
    rw [hd,mul_comm (C^(Fintype.card ι))] at hdet
    exact (mul_le_mul_iff_right₀ hA.det_pos).mp (by simpa only [mul_comm A.det] using hdet)
  let I := Finset.univ.filter (fun i => μ i ≤ C^2)
  let V := Submodule.span ℝ (Set.range (fun i : I => b i.val))
  have hind : LinearIndependent ℝ (fun i : I => b i.val) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have hvdim : Module.finrank ℝ V=I.card := by
    exact (finrank_span_eq_card hind).trans (Fintype.card_coe I)
  refine ⟨V,?_,?_⟩
  · rw [hvdim]
    simpa only [Fintype.card_fin] using many_small_factors μ hμ C hC (by simpa using hp)
  · intro x hx
    rw [hqb,hqa,Finset.mul_sum]
    have hs := basis_support_span b I hx
    apply Finset.sum_le_sum
    intro i hi
    by_cases hiI : i∈I
    · exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hiI).2 (sq_nonneg _)
    · rw [hs i hiI,pow_two,zero_mul,mul_zero,mul_zero]

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousDimension
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.walkFeature_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical Pointwise BigOperators Matrix

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {A ι : Type*} [Fintype ι] (W : Geometry A)

lemma harmonic_functionCombination (v : ι → A → ℝ) (hv : ∀ i, W.IsHarmonic (v i))
    (a : ι → ℝ) : W.IsHarmonic (functionCombination v a) := by
  rw [functionCombination_eq_linearCombination,Fintype.linearCombination_apply]
  change (∑ i, a i • v i)∈W.harmonicSpace
  exact W.harmonicSpace.sum_mem (fun i _ => W.harmonicSpace.smul_mem (a i) (hv i))

lemma scale_ratio_strict (K s L r R : ℕ) (hr : 1 ≤ r)
    (hscale : 10^(2*L)*r ≤ R) (hL : 8*K^4*s < 10^(4*L)) :
    8*(K:ℝ)^4*(s:ℝ)*(r:ℝ)^2 < (R:ℝ)^2 := by
  have hr' : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs : (10:ℝ)^(2*L)*(r:ℝ) ≤ R := by exact_mod_cast hscale
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (10:ℝ)^(2*L)*(r:ℝ)) hs 2
  have hLp : 8*(K:ℝ)^4*(s:ℝ) < (10:ℝ)^(4*L) := by exact_mod_cast hL
  have hh := mul_lt_mul_of_pos_right hLp (sq_pos_of_pos hr')
  have he : ((10:ℝ)^(2*L)*(r:ℝ))^2=(10:ℝ)^(4*L)*(r:ℝ)^2 := by
    rw [mul_pow,←pow_mul (10:ℝ)]
    congr 2
    ring
  rw [he] at hp
  exact hh.trans_le hp

theorem harmonic_independent_card_bound (d k : ℕ) (hg : W.HasDegree d)
    (v : ι → A → ℝ) (hharm : ∀ i, W.IsHarmonic (v i))
    (hpol : ∀ i, W.HasPolynomialGrowth k (v i)) (hli : LinearIndependent ℝ v)
    (L : ℕ) (hL : 0 < L)
    (hgap : 8*(10^(4*(2*d+2*k+1)))^4*W.degree < 10^(4*L)) :
    Fintype.card ι ≤ 2*(10^(4*(2*d+2*k+1)))^L := by
  by_cases hm : Fintype.card ι=0
  · simp only [hm] <;> positivity
  have hm' : 0 < Fintype.card ι := Nat.pos_of_ne_zero hm
  let K : ℕ := 10^(4*(2*d+2*k+1))
  have hK : 1 < (K:ℝ) := by
    have hh : 10 ≤ K := by
      change 10 ≤ 10^(4*(2*d+2*k+1))
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < 10)
        (by omega : 1 ≤ 4*(2*d+2*k+1))
    have hh' : (10:ℝ) ≤ K := by exact_mod_cast hh
    linarith
  obtain ⟨r,R,hr,hR,hrR,hscale,hvol,hdet,hpack,hPD⟩ :=
    W.function_gram_paired_scales d k hg v hpol hli hm' L hL 1
  have hdet' : (functionGram (W.ball (5*R)) v).det ≤
      (K:ℝ)^(Fintype.card ι)*(functionGram (W.ball R) v).det := by
    simpa only [K,Nat.cast_pow,Nat.cast_ofNat] using hdet
  obtain ⟨V,hVdim,hVratio⟩ := exists_low_growth_subspace
    (functionGram (W.ball R) v) (functionGram (W.ball (5*R)) v) hPD
    (functionGram_hermitian _ _) (functionGram_quadratic_mono (W.ball_mono (by omega)) v)
    (K:ℝ) hK hdet'
  obtain ⟨J,hJR,hJ,hJcard,hcover⟩ := W.exists_word_ball_packing R r
  have hJbound : J.card ≤ K^L :=
    le_of_mul_le_mul_right (hJcard.trans hpack) (W.ball_card_pos r)
  have hstrict := scale_ratio_strict K W.degree L r R hr hscale hgap
  let avg : V →ₗ[ℝ] (J → ℝ) :=
    { toFun := fun a c => ∑ x∈W.around c.val (2*r), functionCombination v a.val x
      map_add' := by
        intro a b
        funext c
        simp only [Submodule.coe_add,functionCombination,Pi.add_apply,add_mul,Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        funext c
        simp only [Submodule.coe_smul,functionCombination,Pi.smul_apply,smul_eq_mul,
          mul_assoc,←Finset.mul_sum,RingHom.id_apply] }
  have hInjective : Injective avg := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply Subtype.ext
    by_contra hane
    have hane' : a.val≠0 := hane
    have hQ : 0 < squareMass (W.ball R) (functionCombination v a.val) := by
      have hh := (Matrix.posDef_iff_dotProduct_mulVec.mp hPD).2 hane'
      simpa only [star_trivial,←functionGram_quadratic,matrixQuadratic] using hh
    have havg : ∀ c∈J, (∑ x∈W.around c (2*r), functionCombination v a.val x)=0 := by
      intro c hc
      exact congrFun ha ⟨c,hc⟩
    have hc := W.harmonic_cover_kernel_bound (W.balanced_suborbits d hg) R r K hR hrR J hJR hJ hcover hvol
      (functionCombination v a.val) (W.harmonic_functionCombination v hharm _) havg
    have hl := hVratio a.val a.property
    rw [functionGram_quadratic,functionGram_quadratic] at hl
    have hm := mul_le_mul_of_nonneg_left hl
      (by positivity : 0 ≤ 8*(K:ℝ)^2*(W.degree:ℝ)*(r:ℝ)^2)
    have hlow := mul_lt_mul_of_pos_right hstrict hQ
    nlinarith
  have hdim : Module.finrank ℝ V ≤ J.card := by
    have hh := LinearMap.finrank_le_finrank_of_injective hInjective
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using hh
  exact hVdim.trans (Nat.mul_le_mul_left 2 (hdim.trans hJbound))

omit [Fintype ι] in

theorem polynomialHarmonicSpace_finiteDimensional (d k : ℕ)
    (hg : W.HasDegree d) :
    FiniteDimensional ℝ (W.polynomialHarmonicSpace k) := by
  let K : ℕ := 10^(4*(2*d+2*k+1))
  let L : ℕ := 8*K^4*W.degree+1
  have hL : 0 < L := by dsimp [L]; omega
  have hgap : 8*K^4*W.degree < 10^(4*L) := by
    have hpow : L < 10^L := L.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (by omega) L)
    have hm : 10^L ≤ 10^(4*L) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (by dsimp [L]; omega : 8*K^4*W.degree < L).trans (hpow.trans_le hm)
  let B := 2*K^L
  let H := W.polynomialHarmonicSpace k
  let b := Module.Free.chooseBasis ℝ H
  have hbound {n : ℕ} (w : Fin n → H) (hw : LinearIndependent ℝ w) : n ≤ B := by
    have hj : LinearIndependent ℝ (fun i => (w i:A → ℝ)) :=
      hw.map' H.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hh := W.harmonic_independent_card_bound d k hg (fun i => (w i:A → ℝ))
      (fun i => (w i).property.1) (fun i => (w i).property.2) hj L hL hgap
    simpa only [Fintype.card_fin] using hh
  have hfinite : Finite (Module.Free.ChooseBasisIndex ℝ H) := by
    by_contra h
    let : Infinite (Module.Free.ChooseBasisIndex ℝ H) := not_finite_iff_infinite.mp h
    let e : Fin (B+1) ↪ Module.Free.ChooseBasisIndex ℝ H :=
      (Fin.valEmbedding).trans (Infinite.natEmbedding _)
    have hh := hbound (fun i => b (e i)) (b.linearIndependent.comp e e.injective)
    omega
  let := hfinite
  exact Module.Finite.of_basis b

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_SparseEnergyRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CriticalPercolation.HarmonicAnalysis

lemma exists_small_relative_dissipation (E N : ℕ → ℝ)
    (hpos : ∀ n, 0<E n) (hm : Antitone E)
    (hdis : ∀ n, N n≤E n-E (n+1))
    (d : ℕ) (C : ℝ) (hC : 0≤C)
    (hg : ∀ R, ∃ n≥R, (E n)⁻¹≤C*(n:ℝ)^d)
    (ε : ℝ) (hε : 0<ε) : ∃ n, N n≤ε*E n := by
  by_contra! hbad
  have hmono : Monotone (fun n => (E n)⁻¹) := by
    intro i j hij
    exact (inv_le_inv₀ (hpos i) (hpos j)).mpr (hm hij)
  obtain ⟨R,hR⟩ := exists_nat_gt ((2:ℝ)^(d+1)/ε)
  obtain ⟨r,hr,hgood⟩ := sparse_real_doubling (fun n => (E n)⁻¹) hmono
    0 (fun n _ => inv_pos.mpr (hpos n)) C hC d 2 (by omega) hg R
  have hratio : E r≤(2:ℝ)^(d+1)*E (2*r) := by
    have hh : 1/E (2*r)≤(2:ℝ)^(d+1)/E r := by
      simpa only [Nat.cast_ofNat,one_div,div_eq_mul_inv,one_mul] using hgood
    have hh' := (div_le_div_iff₀ (hpos (2*r)) (hpos r)).mp hh
    simpa only [one_mul] using hh'
  have hεr : (2:ℝ)^(d+1)<(r:ℝ)*ε := by
    have hh : (R:ℝ) ≤ r := by exact_mod_cast (le_max_left R 0).trans hr
    have hh' := (div_lt_iff₀ hε).mp hR
    nlinarith
  have ht : ∀ i ≤ r, (i:ℝ)*ε*E (2*r)≤E r-E (r+i) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have H := ih (by omega)
      have HD := (hbad (r+i)).le.trans (hdis (r+i))
      have HM := mul_le_mul_of_nonneg_left (hm (by omega : r+i≤2*r)) hε.le
      push_cast
      have he : r+(i+1)=r+i+1 := by omega
      rw [he]
      nlinarith
  have hh := ht r le_rfl
  rw [←two_mul] at hh
  have hh' := mul_lt_mul_of_pos_right hεr (hpos (2*r))
  nlinarith [hpos (2*r)]

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_FiniteHilbert
attribute [-simp] _root_.OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.walkState_zero _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.walkFeature_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
open HarmonicAnalysis

variable {X : Type*}

namespace FH
lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → FH X) (x : X) :
    (∑ i∈s, f i) x=∑ i∈s, f i x := by
  simp only [Submodule.coe_sum,lp.coeFn_sum,Finset.sum_apply]

lemma eq_zero_of_not_mem (f : FH X) {x : X} (h : x∉f.support) : f x=0 :=
  not_not.mp ((f.mem_support x).not.mp h)

lemma delta_inner (x : X) (f : FH X) : inner ℝ (delta x) f=f x := by
  change inner ℝ (lp.single 2 x (1:ℝ)) f.val=f x
  rw [lp.inner_single_left]
  simp

lemma inner_eq_sum (f g : FH X) (F : Finset X) (hF : f.support⊆F) :
    inner ℝ f g=∑ x∈F, f x*g x := by
  change (∑' x, inner ℝ (f x) (g x))=_
  simp only [Real.inner_apply]
  apply tsum_eq_sum
  intro x hx
  rw [f.eq_zero_of_not_mem (fun h => hx (hF h)),zero_mul]
lemma norm_sq_eq_sum (f : FH X) (F : Finset X) (hF : f.support⊆F) :
    ‖f‖^2=∑ x∈F, (f x)^2 := by
  rw [←real_inner_self_eq_norm_sq,f.inner_eq_sum f F hF]
  simp only [pow_two]

lemma norm_coordinate_le (f : FH X) (x : X) : |f x|≤‖f‖ := by
  exact lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) f.val x

lemma delta_decomposition (f : FH X) :
    (∑ x∈f.support, f x • delta x)=f := by
  ext y
  rw [sum_apply]
  by_cases hy : y∈f.support
  · simp [delta_apply,hy]
  · simp [delta_apply,hy,f.eq_zero_of_not_mem hy]

lemma sum_sq_le_norm_sq (f : FH X) (F : Finset X) :
    (∑ x∈F, (f x)^2)≤‖f‖^2 := by
  rw [f.norm_sq_eq_sum (F∪f.support) Finset.subset_union_right]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by intros; positivity)

end FH
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphWalkOperator
attribute [-simp] _root_.OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.walkState_zero _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.walkFeature_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma averaging_coordinate (f : FH X) (x : X) :
    W.averaging f x=(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y := rfl

lemma averaging_delta (x : X) : W.averaging (FH.delta x)=
    (W.degree:ℝ)⁻¹ • ∑ y∈W.neighbors x, FH.delta y := by
  ext z
  simp only [W.averaging_coordinate,FH.smul_apply,FH.sum_apply,FH.delta_apply,
    Finset.sum_ite_eq,Finset.sum_ite_eq',W.mem_neighbors]
  congr 1
  congr 1
  exact propext (W.graph.adj_comm _ _)

lemma averaging_symmetric_delta (x : X) (f : FH X) :
    inner ℝ (W.averaging (FH.delta x)) f=inner ℝ (FH.delta x) (W.averaging f) := by
  rw [W.averaging_delta,(real_inner_smul_left (F:=FH X)),sum_inner,FH.delta_inner]
  simp only [FH.delta_inner,W.averaging_coordinate]

lemma averaging_symmetric (f g : FH X) : inner ℝ (W.averaging f) g=inner ℝ f (W.averaging g) := by
  calc
    _ = inner ℝ (W.averaging (∑ x∈f.support, f x • FH.delta x)) g := by rw [f.delta_decomposition]
    _ = ∑ x∈f.support, f x*inner ℝ (W.averaging (FH.delta x)) g := by
      simp only [map_sum,map_smul,sum_inner,(real_inner_smul_left (F:=FH X))]
    _ = inner ℝ (∑ x∈f.support, f x • FH.delta x) (W.averaging g) := by
      simp only [sum_inner,(real_inner_smul_left (F:=FH X)),W.averaging_symmetric_delta]
    _ = _ := by rw [f.delta_decomposition]

lemma sum_neighbor_sq_bound (F : Finset X) (f : FH X) :
    (∑ x∈F, ∑ y∈W.neighbors x, (f y)^2)≤(W.degree:ℝ)*‖f‖^2 := by
  let J := F.biUnion W.neighbors
  have hof : ∀ y∈J, (F.filter (fun x => y∈W.neighbors x)).card≤W.degree := by
    intro y hy
    calc
      _ ≤ (W.neighbors y).card := Finset.card_le_card (by
        intro x hx
        exact W.mem_neighbors.mpr (W.mem_neighbors.mp (Finset.mem_filter.mp hx).2).symm)
      _ = _ := W.neighbors_card y
  have hh := sum_le_sum_of_finite_overlap F W.neighbors J
    (fun x hx y hy => Finset.mem_biUnion.mpr ⟨x,hx,hy⟩) W.degree hof
    (fun y => (f y)^2) (fun y => sq_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_left (f.sum_sq_le_norm_sq J) (Nat.cast_nonneg _))

lemma averaging_norm_le (hD : 0<W.degree) (f : FH X) : ‖W.averaging f‖≤‖f‖ := by
  have hD' : (0:ℝ)<W.degree := by exact_mod_cast hD
  have hpoint (x : X) : (W.averaging f x)^2≤(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, (f y)^2 := by
    have hh := sq_sum_le_card_mul_sum_sq (s:=W.neighbors x) (f:=fun y => f y)
    rw [W.neighbors_card] at hh
    rw [W.averaging_coordinate,mul_pow]
    have he : (W.degree:ℝ)⁻¹^2*(W.degree:ℝ)=(W.degree:ℝ)⁻¹ := by field_simp
    calc
      _ ≤ (W.degree:ℝ)⁻¹^2*((W.degree:ℝ)*∑ y∈W.neighbors x, (f y)^2) :=
        mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = _ := by rw [←mul_assoc,he]
  have hsum := Finset.sum_le_sum (fun x (_ : x∈(W.averaging f).support) => hpoint x)
  rw [←(W.averaging f).norm_sq_eq_sum _ (Finset.Subset.refl _),←Finset.mul_sum] at hsum
  have hbound := mul_le_mul_of_nonneg_left (W.sum_neighbor_sq_bound (W.averaging f).support f)
    (inv_nonneg.mpr hD'.le)
  rw [←mul_assoc,inv_mul_cancel₀ hD'.ne',one_mul] at hbound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsum.trans hbound)

lemma lazyWalk_apply (f : FH X) : W.lazyWalk f=(1/2:ℝ) • (f+W.averaging f) := rfl

lemma lazyWalk_coordinate (f : FH X) (x : X) : W.lazyWalk f x=
    (1/2:ℝ)*(f x+(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y) := rfl

lemma lazyWalk_symmetric (f g : FH X) :
    inner ℝ (W.lazyWalk f) g=inner ℝ f (W.lazyWalk g) := by
  simp only [W.lazyWalk_apply,(real_inner_smul_left (F:=FH X)),(real_inner_smul_right (F:=FH X)),
    inner_add_left,inner_add_right,W.averaging_symmetric]
lemma lazyWalk_norm_le (hD : 0<W.degree) (f : FH X) : ‖W.lazyWalk f‖≤‖f‖ := by
  rw [W.lazyWalk_apply,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have ht := norm_add_le f (W.averaging f)
  have ha := W.averaging_norm_le hD f
  linarith
lemma lazyWalk_positive (hD : 0<W.degree) (f : FH X) : 0 ≤ inner ℝ f (W.lazyWalk f) := by
  have hb := abs_real_inner_le_norm f (W.averaging f)
  have h := mul_le_mul_of_nonneg_left (W.averaging_norm_le hD f) (norm_nonneg f)
  have hl := (abs_le.mp (hb.trans h)).1
  simp only [W.lazyWalk_apply,(real_inner_smul_right (F:=FH X)),inner_add_right,real_inner_self_eq_norm_sq]
  nlinarith
lemma walkEnergy_nonneg (hD : 0<W.degree) (f : FH X) : 0≤W.walkEnergy f := by
  have hb := real_inner_le_norm f (W.lazyWalk f)
  have h := mul_le_mul_of_nonneg_left (W.lazyWalk_norm_le hD f) (norm_nonneg f)
  unfold walkEnergy
  rw [inner_sub_right,real_inner_self_eq_norm_sq]
  nlinarith
lemma walkEnergy_dissipation (hD : 0<W.degree) (f : FH X) :
    ‖f-W.lazyWalk f‖^2≤W.walkEnergy f-W.walkEnergy (W.lazyWalk f) := by
  have hp := W.lazyWalk_positive hD (f-W.lazyWalk f)
  rw [map_sub] at hp
  simp only [inner_sub_left,inner_sub_right] at hp
  rw [←W.lazyWalk_symmetric f (W.lazyWalk f)] at hp
  have hcomm : inner ℝ (W.lazyWalk f) f=inner ℝ f (W.lazyWalk f) := real_inner_comm _ _
  unfold walkEnergy
  simp only [inner_sub_right,real_inner_self_eq_norm_sq,norm_sub_sq_real]
  nlinarith [real_inner_self_eq_norm_sq (W.lazyWalk f)]

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphWalkProbability
attribute [-simp] _root_.OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.walkState_zero _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma degree_pos [Infinite X] : 0<W.degree := by
  obtain ⟨x,hx⟩ := exists_ne W.root
  obtain ⟨p⟩ := W.connected W.root x
  cases p with
  | nil => exact (hx rfl).elim
  | @cons a y z h p => exact Finset.card_pos.mpr ⟨y,W.mem_neighbors.mpr h⟩

lemma averaging_mass (hD : 0<W.degree) (f : FH X) : FH.mass (W.averaging f)=FH.mass f := by
  have hc : (W.degree:ℝ)≠0 := by exact_mod_cast hD.ne'
  have hdelta (x : X) : FH.mass (W.averaging (FH.delta x))=1 := by
    rw [W.averaging_delta,map_smul,map_sum]
    simp only [FH.mass_delta,Finset.sum_const,nsmul_eq_mul,mul_one,smul_eq_mul,W.neighbors_card]
    exact inv_mul_cancel₀ hc
  rw [←f.delta_decomposition]
  simp only [map_sum,map_smul,hdelta,FH.mass_delta]
lemma lazyWalk_nonnegative (f : FH X) (hf : ∀ x, 0≤f x) : ∀ x, 0≤W.lazyWalk f x := by
  intro x
  rw [W.lazyWalk_coordinate]
  exact mul_nonneg (by norm_num) (add_nonneg (hf x)
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun y hy => hf y))))
lemma lazyWalk_mass (hD : 0<W.degree) (f : FH X) : FH.mass (W.lazyWalk f)=FH.mass f := by
  rw [W.lazyWalk_apply,map_smul,map_add,W.averaging_mass hD]
  simp only [smul_eq_mul] <;> ring

lemma walkFeature_succ (n : ℕ) (x : X) : W.walkFeature (n+1) x=W.lazyWalk (W.walkFeature n x) := by
  simp only [walkFeature,pow_succ',Module.End.mul_apply]
lemma walkState_succ (n : ℕ) : W.walkState (n+1)=W.lazyWalk (W.walkState n) := W.walkFeature_succ n W.root
lemma walkState_nonnegative (n : ℕ) : ∀ x, 0≤W.walkState n x := by
  induction n with
  | zero => intro x; simp only [walkState,walkFeature_zero,FH.delta_apply]; split <;> norm_num
  | succ n ih => rw [W.walkState_succ]; exact W.lazyWalk_nonnegative _ ih
lemma walkState_mass (hD : 0<W.degree) (n : ℕ) : FH.mass (W.walkState n)=1 := by
  induction n with
  | zero => exact FH.mass_delta _
  | succ n ih => rw [W.walkState_succ,W.lazyWalk_mass hD,ih]
lemma walkState_root_pos (n : ℕ) : 0<W.walkState n W.root := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate]
    have hs : 0≤(W.degree:ℝ)⁻¹*∑ y∈W.neighbors W.root, W.walkState n y := by
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun y hy => W.walkState_nonnegative n y))
    positivity
lemma walkState_support (n : ℕ) {x : X} (hx : x∉W.ball n) : W.walkState n x=0 := by
  induction n generalizing x with
  | zero =>
    have hne : x≠W.root := by intro h; apply hx; rw [h]; exact W.self_mem_around _ _
    simp [hne]
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate,ih (fun h => hx (W.ball_mono (by omega) h))]
    have hs : (∑ y∈W.neighbors x, W.walkState n y)=0 := by
      apply Finset.sum_eq_zero
      intro y hy
      apply ih
      intro hn
      apply hx
      apply W.mem_around_add hn
      exact W.mem_around.mpr ⟨SimpleGraph.Walk.cons (W.mem_neighbors.mp hy).symm .nil,by simp⟩
    rw [hs]; ring
lemma walkPower_symmetric (n : ℕ) (f g : FH X) :
    inner ℝ ((W.lazyWalk^n) f) g=inner ℝ f ((W.lazyWalk^n) g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    calc
      _ = inner ℝ ((W.lazyWalk^n) (W.lazyWalk f)) g := by rw [pow_succ,Module.End.mul_apply]
      _ = inner ℝ (W.lazyWalk f) ((W.lazyWalk^n) g) := ih _ _
      _ = inner ℝ f (W.lazyWalk ((W.lazyWalk^n) g)) := W.lazyWalk_symmetric _ _
      _ = _ := by rw [pow_succ',Module.End.mul_apply]
lemma walkState_double_at_root (n : ℕ) : W.walkState (2*n) W.root=‖W.walkState n‖^2 := by
  have hh := W.walkPower_symmetric n (FH.delta W.root) (W.walkState n)
  rw [FH.delta_inner] at hh
  have he : (W.lazyWalk^n) (W.walkState n)=W.walkState (2*n) := by
    simp only [walkState,walkFeature,←Module.End.mul_apply,←pow_add,two_mul]
  rw [he] at hh
  change inner ℝ (W.walkState n) (W.walkState n)=_ at hh
  rw [real_inner_self_eq_norm_sq] at hh
  exact hh.symm
lemma walkState_norm_sq (n : ℕ) : ‖W.walkState n‖^2=∑ x∈W.ball n, (W.walkState n x)^2 :=
  (W.walkState n).norm_sq_eq_sum _ (by
    intro x hx; by_contra hn; exact ((W.walkState n).mem_support x).mp hx (W.walkState_support n hn))
lemma walkState_norm_lower (hD : 0<W.degree) (n : ℕ) : 1≤((W.ball n).card:ℝ)*‖W.walkState n‖^2 := by
  have hmass : (∑ x∈W.ball n, W.walkState n x)=1 := by
    rw [←W.walkState_mass hD n]
    exact (tsum_eq_sum (f:=fun x => W.walkState n x) (s:=W.ball n)
      (fun x hx => W.walkState_support n hx)).symm
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (W.ball n) (fun _ => (1:ℝ)) (fun x => W.walkState n x)
  simpa only [one_mul,hmass,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,←W.walkState_norm_sq] using hc

lemma transport_averaging (g : W.Aut) (f : FH X) :
    FH.transport g.toEquiv (W.averaging f)=W.averaging (FH.transport g.toEquiv f) := by
  ext x
  simp only [FH.transport_apply,W.averaging_coordinate]
  congr 1
  change (∑ y∈W.neighbors (g.symm x), f y)=∑ y∈W.neighbors x, f (g.symm y)
  rw [←W.neighbors_image g.symm x,Finset.sum_image]
  exact fun a ha b hb h => g.symm.injective h
lemma transport_lazyWalk (g : W.Aut) (f : FH X) :
    FH.transport g.toEquiv (W.lazyWalk f)=W.lazyWalk (FH.transport g.toEquiv f) := by
  simp only [W.lazyWalk_apply,map_smul,map_add,W.transport_averaging]
lemma transport_walkFeature (g : W.Aut) (n : ℕ) (x : X) :
    FH.transport g.toEquiv (W.walkFeature n x)=W.walkFeature n (g x) := by
  induction n with
  | zero => exact FH.transport_delta _ _
  | succ n ih => rw [W.walkFeature_succ,W.transport_lazyWalk,ih,W.walkFeature_succ]
lemma walkFeature_norm (n : ℕ) (x : X) : ‖W.walkFeature n x‖=‖W.walkState n‖ := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.transport_walkFeature,LinearIsometryEquiv.norm_map]
lemma walkFeature_average (n : ℕ) (x : X) :
    (∑ y∈W.neighbors x, W.walkFeature n y)=(W.degree:ℝ) • W.averaging (W.walkFeature n x) := by
  have hc : W.averaging.comp W.lazyWalk=W.lazyWalk.comp W.averaging := by
    ext f y
    simp only [LinearMap.comp_apply,W.lazyWalk_apply,map_smul,map_add]
  have hcomm : ∀ n, W.averaging.comp (W.lazyWalk^n)=(W.lazyWalk^n).comp W.averaging := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change W.averaging*(W.lazyWalk^(n+1))=(W.lazyWalk^(n+1))*W.averaging
      rw [pow_succ',←mul_assoc,show W.averaging*W.lazyWalk=W.lazyWalk*W.averaging from hc,
        mul_assoc,show W.averaging*W.lazyWalk^n=W.lazyWalk^n*W.averaging from ih,←mul_assoc,←pow_succ']
  have hd (x : X) : (W.degree:ℝ) • W.averaging (FH.delta x)=∑ y∈W.neighbors x, FH.delta y := by
    by_cases hD : W.degree=0
    · have he : W.neighbors x=∅ := Finset.card_eq_zero.mp (by exact (W.neighbors_card x).trans hD)
      simp [hD,he]
    · rw [W.averaging_delta,smul_smul,mul_inv_cancel₀ (by exact_mod_cast hD),one_smul]
  calc
    _ = (W.lazyWalk^n) (∑ y∈W.neighbors x, FH.delta y) := (map_sum _ _ _).symm
    _ = (W.lazyWalk^n) ((W.degree:ℝ) • W.averaging (FH.delta x)) := by rw [hd]
    _ = _ := by rw [map_smul,←LinearMap.comp_apply,←hcomm,LinearMap.comp_apply]; rfl

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphWalkEnergy
attribute [-simp] _root_.OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.walkState_zero _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma exists_ball_boundary [Infinite X] (r : ℕ) : ∃ x∈W.ball (r+1), x∉W.ball r := by
  by_contra! hbad
  have hb (n : ℕ) : W.ball n⊆W.ball r := by
    intro x hx
    obtain ⟨p,hp⟩ := W.mem_around.mp hx
    have hw : ∀ {a b : X}, (p : W.graph.Walk a b) → a∈W.ball r → b∈W.ball r := by
      intro a b p
      induction p with
      | nil => exact id
      | @cons a y b h p ih =>
        intro ha
        apply ih
        apply hbad
        exact W.mem_around_add ha (W.mem_around.mpr ⟨.cons h .nil,by simp⟩)
    exact hw p (W.self_mem_around _ _)
  have hf : (Set.univ:Set X).Finite := (W.ball r).finite_toSet.subset (by
    intro x _; obtain ⟨n,hn⟩ := W.exists_mem_ball x; exact hb n hn)
  exact Set.infinite_univ hf

lemma walkFeature_symmetric (n : ℕ) (x y : X) : W.walkFeature n x y=W.walkFeature n y x := by
  have h := W.walkPower_symmetric n (FH.delta x) (FH.delta y)
  rw [real_inner_comm,FH.delta_inner,FH.delta_inner] at h
  exact h

lemma walkEnergy_gradient (n : ℕ) :
    (∑ y∈W.neighbors W.root, ‖W.walkFeature n y-W.walkState n‖^2)=
      4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by
  simp only [norm_sub_sq_real,W.walkFeature_norm,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum,←sum_inner,W.walkFeature_average,
    real_inner_smul_left (F:=FH X)]
  unfold walkEnergy
  rw [inner_sub_right,W.lazyWalk_apply,real_inner_smul_right (F:=FH X),inner_add_right,
    real_inner_self_eq_norm_sq,W.averaging_symmetric]
  dsimp only [walkState,degree]
  ring

lemma feature_neighbor_bound (hD : 0<W.degree) (n : ℕ) {y : X} (hy : y∈W.neighbors W.root) :
    ‖W.walkFeature n y-W.walkState n‖≤Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  have hh := (Finset.single_le_sum (f:=fun y => ‖W.walkFeature n y-W.walkState n‖^2)
    (fun y hy => sq_nonneg _) hy).trans_eq (W.walkEnergy_gradient n)
  have he : 0≤4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) :=
    mul_nonneg (by positivity) (W.walkEnergy_nonneg hD _)
  nlinarith [Real.sq_sqrt he,Real.sqrt_nonneg (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)),
    norm_nonneg (W.walkFeature n y-W.walkState n)]
lemma feature_edge_bound (hD : 0<W.degree) (n : ℕ) {x y : X} (h : W.graph.Adj x y) :
    ‖W.walkFeature n y-W.walkFeature n x‖≤Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  have he : W.walkFeature n y-W.walkFeature n (g W.root)=
      FH.transport g.toEquiv (W.walkFeature n (g.symm y)-W.walkState n) := by
    rw [map_sub,W.transport_walkFeature,W.transport_walkFeature,g.apply_symm_apply]
  rw [he,LinearIsometryEquiv.norm_map]
  apply W.feature_neighbor_bound hD
  exact W.mem_neighbors.mpr (by simpa using g.symm.map_adj_iff.mpr h)
lemma feature_walk_bound (hD : 0<W.degree) (n : ℕ) {x y : X} (p : W.graph.Walk x y) :
    ‖W.walkFeature n y-W.walkFeature n x‖≤(p.length:ℝ)*Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have he : W.walkFeature n z-W.walkFeature n x=
        (W.walkFeature n z-W.walkFeature n y)+(W.walkFeature n y-W.walkFeature n x) := by abel
    rw [he]
    have ht := norm_add_le (W.walkFeature n z-W.walkFeature n y) (W.walkFeature n y-W.walkFeature n x)
    have hb := W.feature_edge_bound hD n h
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith
lemma feature_ball_bound (hD : 0<W.degree) (n r : ℕ) {x : X} (hx : x∈W.ball r) :
    ‖W.walkFeature n x-W.walkState n‖≤(r:ℝ)*Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  obtain ⟨p,hp⟩ := W.mem_around.mp hx
  exact (W.feature_walk_bound hD n p).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (Real.sqrt_nonneg _))

lemma supported_energy_bound [Infinite X] (n : ℕ) :
    W.walkState n W.root^2≤(n+1:ℝ)^2*4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by
  obtain ⟨x,hx,hx'⟩ := W.exists_ball_boundary n
  have hp := (W.walkFeature n x-W.walkState n).norm_coordinate_le W.root
  have hb := W.feature_ball_bound W.degree_pos n (n+1) hx
  have hv : |(W.walkFeature n x-W.walkState n) W.root|=|W.walkState n W.root| := by
    rw [FH.sub_apply,W.walkFeature_symmetric,W.walkState_support n hx',zero_sub,abs_neg]
  rw [hv] at hp
  have ht := pow_le_pow_left₀ (abs_nonneg _) (hp.trans hb) 2
  have he : 0≤4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) :=
    mul_nonneg (by positivity) (W.walkEnergy_nonneg W.degree_pos _)
  rw [mul_pow,Real.sq_sqrt he,sq_abs] at ht
  push_cast at ht
  nlinarith
lemma walkState_energy_pos [Infinite X] (n : ℕ) : 0<W.walkEnergy (W.walkState n) := by
  have hp := W.walkState_root_pos n
  have hb := W.supported_energy_bound n
  have hn := W.walkEnergy_nonneg W.degree_pos (W.walkState n)
  by_contra! h
  have he := le_antisymm h hn
  rw [he,mul_zero] at hb
  nlinarith
lemma walkState_energy_lower [Infinite X] (n : ℕ) :
    1≤((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.degree:ℝ)*W.walkEnergy (W.walkState (2*n)) := by
  have hn := W.walkState_norm_lower W.degree_pos n
  have hb := W.supported_energy_bound (2*n)
  rw [W.walkState_double_at_root] at hb
  have hsq : 1≤((W.ball n).card:ℝ)^2*(‖W.walkState n‖^2)^2 := by
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hn]
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ((W.ball n).card:ℝ))
  push_cast at hh
  nlinarith
lemma walkState_energy_antitone (hD : 0<W.degree) : Antitone (fun n => W.walkEnergy (W.walkState n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := W.walkEnergy_dissipation hD (W.walkState n)
  rw [←W.walkState_succ] at h
  nlinarith [sq_nonneg ‖W.walkState n-W.lazyWalk (W.walkState n)‖]

lemma walk_energy_inverse_sparse [Infinite X] (d : ℕ)
    (hg : W.HasDegree d) :
    ∃ C : ℝ, 0≤C ∧ ∀ R, ∃ m≥R,
      (W.walkEnergy (W.walkState m))⁻¹≤C*(m:ℝ)^(2*d+2) := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨36*(W.degree:ℝ)*(C:ℝ)^2,by positivity,?_⟩
  intro R
  obtain ⟨n,hn,hvol⟩ := hC (max R 1)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hnR : R≤n := (le_max_left R 1).trans hn
  refine ⟨2*n,by omega,?_⟩
  have hV : ((W.ball n).card:ℝ)≤(C:ℝ)*(n:ℝ)^d := by exact_mod_cast hvol
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpoly : ((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.degree:ℝ)≤
      (36*(W.degree:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2) := by
    calc
      _ ≤ ((C:ℝ)*(n:ℝ)^d)^2*(3*(n:ℝ))^2*4*(W.degree:ℝ) := by
        gcongr
        linarith
      _ = (36*(W.degree:ℝ)*(C:ℝ)^2)*(n:ℝ)^(2*d+2) := by
        rw [pow_add,pow_mul]
        ring
      _ ≤ _ := by
        gcongr
        linarith
  have hb := W.walkState_energy_lower n
  have hh := mul_le_mul_of_nonneg_right hpoly (W.walkState_energy_pos (2*n)).le
  have hf : 1≤((36*(W.degree:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2))*
      W.walkEnergy (W.walkState (2*n)) := hb.trans hh
  exact (inv_le_iff_one_le_mul₀ (W.walkState_energy_pos (2*n))).mpr hf

theorem exists_walk_small_relative_residual [Infinite X] (d : ℕ)
    (hg : W.HasDegree d) (ε : ℝ) (hε : 0<ε) :
    ∃ n, 0<W.walkEnergy (W.walkState n) ∧
      ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2≤ε*W.walkEnergy (W.walkState n) := by
  obtain ⟨C,hC,hpoly⟩ := W.walk_energy_inverse_sparse d hg
  obtain ⟨n,hn⟩ := exists_small_relative_dissipation
    (fun n => W.walkEnergy (W.walkState n))
    (fun n => ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2)
    W.walkState_energy_pos (W.walkState_energy_antitone W.degree_pos)
    (fun n => by simpa only [W.walkState_succ] using W.walkEnergy_dissipation W.degree_pos (W.walkState n))
    (2*d+2) C hC hpoly ε hε
  exact ⟨n,W.walkState_energy_pos n,hn⟩

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphProjectedFunctions
attribute [-simp] _root_.OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.walkState_zero _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma exists_large_neighbor_gradient (hD : 0<W.degree) (n : ℕ) :
    ∃ t∈W.neighbors W.root, 4*W.walkEnergy (W.walkState n)≤‖W.walkFeature n t-W.walkState n‖^2 := by
  by_contra! h
  have hh := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hD) (fun t ht => h t ht)
  rw [W.walkEnergy_gradient] at hh
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  nlinarith
lemma projectedFunction_root (n : ℕ) (t : X) : W.projectedFunction n t W.root=0 := by
  simp [projectedFunction,walkState]
lemma projectedFunction_edge_bound [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) {x y : X} (hxy : W.graph.Adj x y) :
    |W.projectedFunction n t y-W.projectedFunction n t x|≤1 := by
  let q := 4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<q := by dsimp [q] <;> positivity
  have he : (W.walkFeature n y-W.walkState n)-(W.walkFeature n x-W.walkState n)=
      W.walkFeature n y-W.walkFeature n x := by abel
  unfold projectedFunction
  rw [←sub_div,←inner_sub_left,he,abs_div,abs_of_pos hq]
  apply (div_le_one hq).mpr
  calc
    _ ≤ ‖W.walkFeature n y-W.walkFeature n x‖*‖W.walkFeature n t-W.walkState n‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt q*Real.sqrt q := mul_le_mul (W.feature_edge_bound W.degree_pos n hxy)
      (W.feature_neighbor_bound W.degree_pos n ht) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = q := Real.mul_self_sqrt hq.le
lemma projectedFunction_length_bound [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) (x : X) : |W.projectedFunction n t x|≤(W.length x:ℝ) := by
  let q := 4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<q := by dsimp [q] <;> positivity
  unfold projectedFunction
  rw [abs_div,abs_of_pos hq]
  apply (div_le_iff₀ hq).mpr
  calc
    _ ≤ ‖W.walkFeature n x-W.walkState n‖*‖W.walkFeature n t-W.walkState n‖ := abs_real_inner_le_norm _ _
    _ ≤ ((W.length x:ℝ)*Real.sqrt q)*Real.sqrt q :=
      mul_le_mul (W.feature_ball_bound W.degree_pos n _ (W.mem_ball_length x))
        (W.feature_neighbor_bound W.degree_pos n ht) (norm_nonneg _) (by positivity)
    _ = (W.length x:ℝ)*q := by rw [mul_assoc,Real.mul_self_sqrt hq.le]
lemma projectedFunction_neighbor_lower [Infinite X] (n : ℕ) (t : X)
    (ht : 4*W.walkEnergy (W.walkState n)≤‖W.walkFeature n t-W.walkState n‖^2) :
    (W.degree:ℝ)⁻¹≤W.projectedFunction n t t := by
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by positivity
  unfold projectedFunction
  rw [real_inner_self_eq_norm_sq]
  apply (le_div_iff₀ hq).mpr
  have he : (W.degree:ℝ)⁻¹*(4*(W.degree:ℝ)*W.walkEnergy (W.walkState n))=4*W.walkEnergy (W.walkState n) := by field_simp
  rw [he]; exact ht
lemma sum_feature_displacement (n : ℕ) (x : X) :
    (∑ y∈W.neighbors x, (W.walkFeature n x-W.walkFeature n y))=
      (2*(W.degree:ℝ)) • (W.walkFeature n x-W.lazyWalk (W.walkFeature n x)) := by
  rw [Finset.sum_sub_distrib,Finset.sum_const,←Nat.cast_smul_eq_nsmul ℝ,
    W.neighbors_card,W.walkFeature_average,W.lazyWalk_apply]
  module
lemma projectedFunction_residual (n : ℕ) (t x : X) :
    (∑ y∈W.neighbors x, (W.projectedFunction n t x-W.projectedFunction n t y))=
      (2*(W.degree:ℝ))*inner ℝ (W.walkFeature n x-W.lazyWalk (W.walkFeature n x))
        (W.walkFeature n t-W.walkState n)/(4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  simp only [projectedFunction,←sub_div,←Finset.sum_div,←inner_sub_left,←sum_inner]
  have he : (∑ y∈W.neighbors x, (W.walkFeature n x-W.walkState n-(W.walkFeature n y-W.walkState n)))=
      ∑ y∈W.neighbors x, (W.walkFeature n x-W.walkFeature n y) := by
    apply Finset.sum_congr rfl; intros; abel
  rw [he,W.sum_feature_displacement,real_inner_smul_left (F:=FH X)]
lemma feature_residual_norm (n : ℕ) (x : X) :
    ‖W.walkFeature n x-W.lazyWalk (W.walkFeature n x)‖=‖W.walkState n-W.lazyWalk (W.walkState n)‖ := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.transport_walkFeature,←W.transport_lazyWalk,←map_sub,LinearIsometryEquiv.norm_map]
lemma projectedFunction_residual_sq [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) (x : X) :
    (∑ y∈W.neighbors x, (W.projectedFunction n t x-W.projectedFunction n t y))^2≤
      (W.degree:ℝ)*‖W.walkState n-W.lazyWalk (W.walkState n)‖^2/W.walkEnergy (W.walkState n) := by
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hgrad := (Finset.single_le_sum (f:=fun y => ‖W.walkFeature n y-W.walkState n‖^2)
    (fun y hy => sq_nonneg _) ht).trans_eq (W.walkEnergy_gradient n)
  have hi := abs_real_inner_le_norm (W.walkFeature n x-W.lazyWalk (W.walkFeature n x))
    (W.walkFeature n t-W.walkState n)
  rw [W.feature_residual_norm] at hi
  have hisq := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [sq_abs,mul_pow] at hisq
  have hb := mul_le_mul_of_nonneg_left hgrad (sq_nonneg ‖W.walkState n-W.lazyWalk (W.walkState n)‖)
  rw [W.projectedFunction_residual,div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos (show 0<4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) by positivity)) hf).mpr
  have hm := mul_le_mul_of_nonneg_left (hisq.trans hb)
    (show 0≤4*(W.degree:ℝ)^2*W.walkEnergy (W.walkState n) by positivity)
  nlinarith only [hm]
end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphHarmonicCompactness
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.walkState_zero _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter
open scoped Classical Pointwise BigOperators Topology

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
variable {A : Type*} (W : Geometry A)

include W in
lemma countable_vertices : Countable A := by
  apply Set.countable_univ_iff.mp
  have hc : (⋃ n:ℕ, (W.ball n:Set A)).Countable :=
    Set.countable_iUnion (fun n => (W.ball n).finite_toSet.countable)
  apply hc.mono
  intro a _
  obtain ⟨n,hn⟩ := W.exists_mem_ball a
  exact Set.mem_iUnion.mpr ⟨n,hn⟩

lemma exists_projected_approximation [Infinite A] (d : ℕ)
    (hg : W.HasDegree d) (δ : ℝ) (hδ : 0<δ) :
    ∃ u : A → ℝ, u W.root=0 ∧ (∀ x, |u x|≤(W.length x:ℝ)) ∧
      (∀ x y, W.graph.Adj x y → |u y-u x|≤1) ∧
      (W.degree:ℝ)⁻¹^2≤∑ s∈W.neighbors W.root, (u s)^2 ∧
      ∀ x, |∑ s∈W.neighbors x, (u x-u s)|≤δ := by
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  obtain ⟨n,hE,hres⟩ := W.exists_walk_small_relative_residual d hg
    (δ^2/(W.degree:ℝ)) (div_pos (sq_pos_of_pos hδ) hc)
  let f := W.walkState n
  obtain ⟨t,ht,hlarge⟩ := W.exists_large_neighbor_gradient W.degree_pos n
  let u := W.projectedFunction n t
  have hlow := W.projectedFunction_neighbor_lower n t hlarge
  refine ⟨u,W.projectedFunction_root n t,W.projectedFunction_length_bound n t ht,
    fun x y h => W.projectedFunction_edge_bound n t ht h,?_,?_⟩
  · have hs : (W.degree:ℝ)⁻¹^2≤(u t)^2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hc.le) hlow 2
    exact hs.trans (Finset.single_le_sum (fun s hs => sq_nonneg (u s)) ht)
  · intro x
    have h := W.projectedFunction_residual_sq n t ht x
    have hb : (W.degree:ℝ)*‖f-W.lazyWalk f‖^2/W.walkEnergy f≤δ^2 := by
      apply (div_le_iff₀ hE).mpr
      have hh := mul_le_mul_of_nonneg_left hres hc.le
      have he : (W.degree:ℝ)*(δ^2/(W.degree:ℝ)*W.walkEnergy f)=δ^2*W.walkEnergy f := by
        field_simp
      rw [he] at hh
      exact hh
    have hh : (∑ s∈W.neighbors x, (u x-u s))^2≤δ^2 := h.trans hb
    nlinarith [sq_abs (∑ s∈W.neighbors x, (u x-u s)),abs_nonneg (∑ s∈W.neighbors x, (u x-u s))]

theorem exists_nonconstant_lipschitz_harmonic [Infinite A] (d : ℕ)
    (hg : W.HasDegree d) :
    ∃ u : A → ℝ, W.IsHarmonic u ∧ u W.root=0 ∧
      (∀ x, |u x|≤(W.length x:ℝ)) ∧
      (∀ x y, W.graph.Adj x y → |u y-u x|≤1) ∧
      ∃ s∈W.neighbors W.root, u s≠0 := by
  let _ : Countable A := W.countable_vertices
  have hδ (n:ℕ) : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  choose v hv1 hvbound hvedge hvgrad hvres using
    (fun n : ℕ => W.exists_projected_approximation d hg (1/((n:ℝ)+1)) (hδ n))
  let K : Set (A → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-(W.length x:ℝ)) (W.length x:ℝ))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hvK (n:ℕ) : v n∈K := by
    intro x hx
    exact abs_le.mp (hvbound n x)
  obtain ⟨u,huK,φ,hφ,hlim⟩ := hK.tendsto_subseq hvK
  have hxlim (x:A) : Tendsto (fun n => v (φ n) x) atTop (𝓝 (u x)) :=
    (continuous_apply x).continuousAt.tendsto.comp hlim
  have hu1 : u W.root=0 := by
    have hh : Tendsto (fun n => v (φ n) W.root) atTop (𝓝 0) := by
      simpa only [hv1] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hxlim W.root) hh
  have hbound (x:A) : |u x|≤(W.length x:ℝ) := abs_le.mpr (huK x (Set.mem_univ x))
  have hedge (x y:A) (h:W.graph.Adj x y) : |u y-u x|≤1 :=
    le_of_tendsto ((hxlim y).sub (hxlim x)).abs (Filter.Eventually.of_forall (fun n => hvedge (φ n) x y h))
  have hgrad : (W.degree:ℝ)⁻¹^2≤∑ s∈W.neighbors W.root, (u s)^2 := by
    have hl := tendsto_finsetSum (W.neighbors W.root) (fun s hs => (hxlim s).pow 2)
    exact ge_of_tendsto hl (Filter.Eventually.of_forall (fun n => hvgrad (φ n)))
  have hharm : W.IsHarmonic u := by
    intro x
    have hl := tendsto_finsetSum (W.neighbors x) (fun s hs => (hxlim x).sub (hxlim s))
    have hz : Tendsto (fun n : ℕ => 1/((φ n:ℝ)+1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    have hnonneg : (0:ℝ)≤ |∑ s∈W.neighbors x, (u x-u s)| := abs_nonneg _
    have hle : |∑ s∈W.neighbors x, (u x-u s)|≤0 :=
      le_of_tendsto_of_tendsto hl.abs hz (Filter.Eventually.of_forall (fun n => hvres (φ n) x))
    exact abs_eq_zero.mp (le_antisymm hle hnonneg)
  refine ⟨u,hharm,hu1,hbound,hedge,?_⟩
  by_contra! hn
  have hz : (∑ s∈W.neighbors W.root, (u s)^2)=0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [hn s hs]
    norm_num
  rw [hz] at hgrad
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hp := sq_pos_of_pos (inv_pos.mpr hc)
  linarith

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphHarmonicLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma harmonic_constant_of_attained_max {u : X → ℝ} (hu : W.IsHarmonic u)
    (a : X) (hmax : ∀ x, u x≤u a) : ∀ x, u x=u a := by
  have hstep {x y : X} (hx : u x=u a) (hxy : W.graph.Adj x y) : u y=u a := by
    have hn (z : X) (hz : z∈W.neighbors x) : 0≤u x-u z := by rw [hx]; exact sub_nonneg.mpr (hmax z)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp (hu x) y (W.mem_neighbors.mpr hxy)
    linarith
  have hw : ∀ {x y : X}, W.graph.Walk x y → u x=u a → u y=u a := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z h p ih => exact fun hx => ih (hstep hx h)
  intro x
  obtain ⟨p⟩ := W.connected a x
  exact hw p rfl
lemma harmonic_constant_of_finite_range {u : X → ℝ} (hu : W.IsHarmonic u)
    (hf : (Set.range u).Finite) : ∀ x, u x=u W.root := by
  let : Nonempty X := ⟨W.root⟩
  obtain ⟨m,⟨a,rfl⟩,hm⟩ := Set.exists_max_image (Set.range u) id hf (Set.range_nonempty u)
  have he := W.harmonic_constant_of_attained_max hu a (fun x => hm (u x) ⟨x,rfl⟩)
  exact fun x => (he x).trans (he W.root).symm

lemma harmonicTranslation_eq_of_agree (k r : ℕ)
    (hdet : ∀ u : W.polynomialHarmonicSpace k, (∀ x∈W.ball r, (u:X → ℝ) x=0) → u=0)
    (a b : W.Aut) (hab : ∀ x∈W.ball r, a.symm x=b.symm x) :
    W.harmonicRepresentation k a=W.harmonicRepresentation k b := by
  apply LinearEquiv.ext
  intro u
  apply sub_eq_zero.mp
  apply hdet
  intro x hx
  change (u:X → ℝ) (a.symm x)-(u:X → ℝ) (b.symm x)=0
  rw [hab x hx,sub_self]

lemma finite_stabilizer_harmonic_image (d k : ℕ) (hg : W.HasDegree d) :
    (Set.range (fun a : W.Stab => W.harmonicRepresentation k a.val)).Finite := by
  let _ := W.polynomialHarmonicSpace_finiteDimensional d k hg
  obtain ⟨r,hr⟩ := exists_detecting_ball (fun r => (W.ball r:Set X)) W.ball_mono W.exists_mem_ball
    (W.polynomialHarmonicSpace k)
  obtain ⟨H,iH,fH,t,ht,hs⟩ := exists_finite_restriction (G:=W.Stab) (W.ball r:Set X)
    (W.ball r).finite_toSet (W.stab_ball_preserved r)
  let _ := iH
  let _ := fH
  apply (Set.finite_range (fun h : H => W.harmonicRepresentation k (t h).val⁻¹)).subset
  rintro _ ⟨a,rfl⟩
  obtain ⟨h,hh⟩ := hs a⁻¹
  refine ⟨h,?_⟩
  apply W.harmonicTranslation_eq_of_agree k r hr
  intro x hx
  exact hh x hx

variable {G : Type*} [Group G] (τ : G →* W.Aut)
lemma finite_range_of_finite_harmonic_image (k : ℕ)
    (htrans : ∀ x, ∃ a : G, τ a W.root=x)
    (hf : (Set.range ((W.harmonicRepresentation k).comp τ)).Finite) (u : W.polynomialHarmonicSpace k) :
    (Set.range (u:X → ℝ)).Finite := by
  apply (hf.image (fun e => (e u:X → ℝ) W.root)).subset
  rintro y ⟨x,rfl⟩
  obtain ⟨a,ha⟩ := htrans x
  refine ⟨(W.harmonicRepresentation k).comp τ a⁻¹,⟨a⁻¹,rfl⟩,?_⟩
  change (u:X → ℝ) ((τ a⁻¹).symm W.root)=(u:X → ℝ) x
  rw [map_inv]
  change (u:X → ℝ) (τ a W.root)=(u:X → ℝ) x
  rw [ha]
lemma infinite_harmonic_linear_image [Infinite X] (d : ℕ) (hg : W.HasDegree d)
    (htrans : ∀ x, ∃ a : G, τ a W.root=x) :
    (Set.range ((W.harmonicRepresentation 1).comp τ)).Infinite := by
  obtain ⟨u,hu,hu1,hbound,hedge,s,hs,hne⟩ := W.exists_nonconstant_lipschitz_harmonic d hg
  have hupol : W.HasPolynomialGrowth 1 u := by
    apply (W.polynomial_growth_iff_length 1 u).mpr
    refine ⟨1,by norm_num,?_⟩
    intro x
    simpa only [pow_one,one_mul] using (hbound x).trans (by linarith : (W.length x:ℝ)≤(W.length x:ℝ)+1)
  let v : W.polynomialHarmonicSpace 1 := ⟨u,hu,hupol⟩
  intro hf
  have hconst := W.harmonic_constant_of_finite_range hu
    (W.finite_range_of_finite_harmonic_image τ 1 htrans hf v)
  exact hne ((hconst s).trans hu1)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_AlgebraicVirtualSolvability
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

lemma finiteIndex_comap_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Surjective f) (P : Subgroup B) [P.FiniteIndex] :
    (P.comap f).FiniteIndex := by
  constructor
  rw [Subgroup.index_comap,f.range_eq_top_of_surjective hf,Subgroup.relIndex_top_right]
  exact Subgroup.FiniteIndex.index_ne_zero

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetIndicability
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma finite_image_to_integer_ker (K : Subgroup A) (f : A →* Multiplicative ℤ)
    (hf : (f '' (K:Set A)).Finite) : K≤f.ker := by
  let J := K.map f
  let : Finite J := hf.to_subtype
  intro k hk
  let j : J := ⟨f k,Subgroup.mem_map.mpr ⟨k,hk,rfl⟩⟩
  obtain ⟨n,hn,he⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite j)
  have hm : (f k)^n=1 := congrArg Subtype.val he
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hm⟩).eq_one'

lemma indicability_pullback_killing (K : Subgroup A) (f : A →* B) (hf : Surjective f)
    (hK : (f '' (K:Set A)).Finite)
    (hb : ∃ P : Subgroup B, P.FiniteIndex ∧ ∃ q : P →* Multiplicative ℤ, Surjective q) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ K.subgroupOf H≤q.ker := by
  obtain ⟨P,hPi,q,hq⟩ := hb
  let := hPi
  let H := P.comap f
  let ψ : H →* P := (f.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Surjective ψ := by
    intro p
    obtain ⟨a,ha⟩ := hf p.val
    refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
    change f a∈P
    rw [ha]
    exact p.property
  refine ⟨H,LinearGrowth.finiteIndex_comap_surjective f hf P,q.comp ψ,hq.comp hψ,?_⟩
  apply finite_image_to_integer_ker
  change ((fun h => q (ψ h)) '' (K.subgroupOf H:Set H)).Finite
  rw [←Set.image_image q ψ]
  apply Set.Finite.image
  apply Set.Finite.of_finite_image (f:=P.subtype)
  · apply hK.subset
    rintro _ ⟨p,⟨h,hh,rfl⟩,rfl⟩
    exact ⟨h.val,hh,rfl⟩
  · exact P.subtype_injective.injOn

lemma Presentation.virtually_indicable (P : Presentation A) (d : ℕ)
    (hg : HasDegree P.K P.S d) [Infinite P.X] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ P.K.subgroupOf H≤q.ker := by
  let W := P.geometry (hg.1 1)
  let ρ := (W.harmonicRepresentation 1).comp P.actionHom
  have hWg : W.HasDegree d := P.geometry_hasDegree d hg
  have htrans : ∀ x : P.X, ∃ a : A, P.actionHom a W.root=x := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨a,by change P.projection (a*1)=P.projection a; rw [mul_one]⟩
  have hInf : (Set.range ρ).Infinite := W.infinite_harmonic_linear_image P.actionHom d hWg htrans
  have hKρ : (ρ '' (P.K:Set A)).Finite := by
    apply (W.finite_stabilizer_harmonic_image d 1 hWg).subset
    rintro _ ⟨k,hk,rfl⟩
    have hstab : P.actionHom k∈W.Stab := by
      change P.projection (k*1)=P.projection 1
      apply QuotientGroup.eq.mpr
      simpa using P.K.inv_mem hk
    exact ⟨⟨P.actionHom k,hstab⟩,rfl⟩
  let f := ρ.rangeRestrict
  have hKf : (f '' (P.K:Set A)).Finite := by
    apply Set.Finite.of_finite_image (f:=ρ.range.subtype)
    · simpa only [Set.image_image] using (show ((fun x => ρ.range.subtype (f x)) '' (P.K:Set A)).Finite from hKρ)
    · exact ρ.range.subtype_injective.injOn
  have hgR := hg.image_polynomial P.one_mem P.inv_eq P.generates f ρ.rangeRestrict_surjective hKf
  let : Infinite ρ.range := hInf.to_subtype
  exact indicability_pullback_killing P.K f ρ.rangeRestrict_surjective hKf hgR.linear_virtually_indicable

lemma virtually_indicable_oai {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hg : HasDegree K S d) [Infinite (A ⧸ K)] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ K.subgroupOf H≤q.ker := by
  obtain ⟨P,hPK,hPb,hSP⟩ := normalized_generators K S h1 hi hgen hK
  have hgP : HasDegree P.K P.S d := hPK.symm ▸ hg.bounded_generators h1 hPb
  let : Infinite P.X := by change Infinite (A ⧸ P.K); rw [hPK]; infer_instance
  exact hPK ▸ P.virtually_indicable d hgP

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_oai.{u_1} := @OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_oai.{u_1}
