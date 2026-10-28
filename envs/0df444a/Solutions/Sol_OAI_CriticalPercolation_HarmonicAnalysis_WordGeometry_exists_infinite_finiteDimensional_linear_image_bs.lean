-- Prove2me | solution 1 for OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:01:01.255805+00:00
-- url     : https://prove2.me/submissions/25275a4b-c76a-4d0b-be97-b23ed1513d31

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_PairedSparseScales
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
  have hK : 0 < K := by dsimp [K]; positivity
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteCoverSums
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_SparseEnergyRatio
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_WordLengthGeometry
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

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

namespace WordGeometry
variable (W : WordGeometry A)

lemma ball_mono : Monotone W.ball := by
  intro m n h
  exact Finset.pow_subset_pow_right W.one_mem h

lemma length_generator {s : A} (hs : s∈W.generators) : W.length s≤1 :=
  W.length_le_iff.mpr (by simpa [ball] using hs)

lemma length_mul_generator {s : A} (hs : s∈W.generators) (a : A) :
    W.length (a*s)≤W.length a+1 ∧ W.length a≤W.length (a*s)+1 := by
  constructor
  · exact (W.length_mul_le a s).trans (Nat.add_le_add_left (W.length_generator hs) _)
  · have hh := W.length_mul_le (a*s) s⁻¹
    rw [mul_inv_cancel_right,W.length_inv] at hh
    exact hh.trans (Nat.add_le_add_left (W.length_generator hs) _)

lemma cutoff_nonneg (R : ℕ) (a : A) : 0≤W.cutoff R a := le_max_left _ _

lemma cutoff_large (R : ℕ) {a : A} (ha : a∈W.ball R) : (R:ℝ)≤W.cutoff R a := by
  have hl : (W.length a:ℝ)≤R := by exact_mod_cast W.length_le_iff.mpr ha
  exact (by linarith : (R:ℝ)≤2*R-W.length a).trans (le_max_right _ _)

lemma cutoff_eq_zero (R : ℕ) {a : A} (ha : 2*R≤W.length a) : W.cutoff R a=0 := by
  have hl : 2*(R:ℝ)≤W.length a := by exact_mod_cast ha
  exact max_eq_left (by linarith)

lemma cutoff_ne_zero_length (R : ℕ) {a : A} (ha : W.cutoff R a≠0) :
    W.length a<2*R := by
  by_contra! h
  exact ha (W.cutoff_eq_zero R h)

lemma cutoff_lipschitz_generator (R : ℕ) {s : A} (hs : s∈W.generators) (a : A) :
    |W.cutoff R (a*s)-W.cutoff R a|≤1 := by
  obtain ⟨h1,h2⟩ := W.length_mul_generator hs a
  have h1' : (W.length (a*s):ℝ)≤(W.length a:ℝ)+1 := by exact_mod_cast h1
  have h2' : (W.length a:ℝ)≤(W.length (a*s):ℝ)+1 := by exact_mod_cast h2
  unfold cutoff
  rw [abs_le]
  constructor <;> rcases le_total 0 (2*(R:ℝ)-W.length (a*s)) with hx|hx <;>
    rcases le_total 0 (2*(R:ℝ)-W.length a) with hy|hy <;>
    simp only [max_eq_right hx,max_eq_left hx,max_eq_right hy,max_eq_left hy] <;> linarith

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_WordBallPacking
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

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma mem_around_iff {a x : A} {r : ℕ} : x∈W.around a r ↔ a⁻¹*x∈W.ball r := by
  constructor
  · intro h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
    simpa using hy
  · intro h
    exact Finset.mem_image.mpr ⟨a⁻¹*x,h,mul_inv_cancel_left a x⟩

lemma mem_ball_inv {x : A} {r : ℕ} (hx : x∈W.ball r) : x⁻¹∈W.ball r := by
  have hh := Finset.inv_mem_inv hx
  simpa [ball,←inv_pow,W.inv_eq] using hh

lemma self_mem_around (a : A) (r : ℕ) : a∈W.around a r := by
  rw [W.mem_around_iff]
  simp only [inv_mul_cancel]
  exact Finset.one_mem_pow W.one_mem

lemma card_around (a : A) (r : ℕ) : (W.around a r).card=(W.ball r).card := by
  unfold around
  exact Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h)

lemma mem_around_symm {a x : A} {r : ℕ} (hx : x∈W.around a r) : a∈W.around x r := by
  rw [W.mem_around_iff] at hx ⊢
  simpa only [mul_inv_rev,inv_inv] using W.mem_ball_inv hx

lemma mem_around_add {a x y : A} {r s : ℕ}
    (hx : x∈W.around a r) (hy : y∈W.around x s) : y∈W.around a (r+s) := by
  rw [W.mem_around_iff] at hx hy ⊢
  rw [ball,pow_add]
  exact Finset.mem_mul.mpr ⟨a⁻¹*x,hx,x⁻¹*y,hy,by simp [mul_assoc]⟩

lemma around_subset_ball {a : A} {R r : ℕ} (ha : a∈W.ball R) :
    W.around a r⊆W.ball (R+r) := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  rw [ball,pow_add]
  exact Finset.mem_mul.mpr ⟨a,ha,y,hy,rfl⟩

lemma ball_card_pos (r : ℕ) : 0<(W.ball r).card :=
  Finset.card_pos.mpr ⟨1,Finset.one_mem_pow W.one_mem⟩

lemma packing_card_bound (J : Finset A) (r : ℕ)
    (hJ : (J:Set A).PairwiseDisjoint (fun a => W.around a r))
    (F : Finset A) (hF : ∀ a∈J, W.around a r⊆F) :
    J.card*(W.ball r).card≤F.card := by
  calc
    _ = ∑ a∈J, (W.around a r).card := by simp only [W.card_around,Finset.sum_const_nat]
    _ = (J.biUnion (fun a => W.around a r)).card := (Finset.card_biUnion hJ).symm
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      obtain ⟨a,ha,hx⟩ := Finset.mem_biUnion.mp hx
      exact hF a ha hx)

theorem exists_word_ball_packing (R r : ℕ) :
    ∃ J : Finset A, J⊆W.ball R ∧
      (J:Set A).PairwiseDisjoint (fun a => W.around a r) ∧
      J.card*(W.ball r).card≤(W.ball (R+r)).card ∧
      ∀ x∈W.ball R, ∃ a∈J, x∈W.around a (2*r) := by
  let C : Finset (Finset A) := (W.ball R).powerset.filter
    (fun (J : Finset A) => (J:Set A).PairwiseDisjoint (fun a => W.around a r))
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

lemma packing_overlap (J : Finset A) (r t K : ℕ)
    (hJ : (J:Set A).PairwiseDisjoint (fun a => W.around a r))
    (hvol : (W.ball (t+r)).card≤K*(W.ball r).card) (x : A) :
    (J.filter (fun a => x∈W.around a t)).card≤K := by
  let I := J.filter (fun a => x∈W.around a t)
  have hIJ : I⊆J := Finset.filter_subset _ _
  have hId : (I:Set A).PairwiseDisjoint (fun a => W.around a r) := fun a ha b hb hab => hJ (hIJ ha) (hIJ hb) hab
  have hsub (a : A) (ha : a∈I) : W.around a r⊆W.around x (t+r) := by
    intro y hy
    exact W.mem_around_add (W.mem_around_symm (Finset.mem_filter.mp ha).2) hy
  have hh := W.packing_card_bound I r hId (W.around x (t+r)) hsub
  rw [W.card_around] at hh
  exact le_of_mul_le_mul_right (hh.trans hvol) (W.ball_card_pos r)

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_CayleyPoincare
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

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A] [DecidableEq A]

omit [DecidableEq A] in
lemma energy_nonneg (S F : Finset A) (u : A → ℝ) : 0≤energy S F u := by
  exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun s _ => sq_nonneg _))

omit [DecidableEq A] in
lemma energy_mono (S : Finset A) {F H : Finset A} (h : F⊆H) (u : A → ℝ) :
    energy S F u≤energy S H u := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro x _ _
  exact Finset.sum_nonneg (fun s _ => sq_nonneg _)

lemma shifted_gradient_le_energy (S : Finset A) (u : A → ℝ)
    (r n : ℕ) (a s : A) (ha : a∈S^n) (hs : s∈S) :
    (∑ x∈S^r, (u ((x*a)*s)-u (x*a))^2)≤energy S (S^(r+n)) u := by
  let F := (S^r).image (fun x => x*a)
  have hF : F⊆S^(r+n) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    rw [pow_add]
    exact Finset.mem_mul.mpr ⟨x,hx,a,ha,rfl⟩
  calc
    _ = ∑ y∈F, (u (y*s)-u y)^2 := by
      rw [Finset.sum_image]
      intro x _ y _ h
      exact mul_right_cancel h
    _ ≤ energy S F u := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.single_le_sum (f := fun b : A => (u (x*b)-u x)^2)
        (fun b _ => sq_nonneg _) hs
    _ ≤ energy S (S^(r+n)) u := energy_mono S hF u

lemma word_difference_energy (S : Finset A) (h1 : (1:A)∈S)
    (u : A → ℝ) (r n : ℕ) (a : A) (ha : a∈S^n) :
    (∑ x∈S^r, (u (x*a)-u x)^2)≤(n:ℝ)^2*energy S (S^(r+n)) u := by
  induction n generalizing a with
  | zero =>
    have he : a=1 := by simpa using ha
    simp [he]
  | succ n ih =>
    rw [pow_succ] at ha
    obtain ⟨b,hb,s,hs,rfl⟩ := Finset.mem_mul.mp ha
    let E := energy S (S^(r+(n+1))) u
    have hmono : energy S (S^(r+n)) u≤E :=
      energy_mono S (Finset.pow_subset_pow_right h1 (by omega)) u
    have hbnd : (∑ x∈S^r, (u (x*b)-u x)^2)≤(n:ℝ)^2*E :=
      (ih b hb).trans (mul_le_mul_of_nonneg_left hmono (sq_nonneg _))
    have hsnd : (∑ x∈S^r, (u ((x*b)*s)-u (x*b))^2)≤E :=
      (shifted_gradient_le_energy S u r n b s hb hs).trans hmono
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      have he : b=1 := by simpa using hb
      simpa [he,E] using hsnd
    · have hn' : (0:ℝ)<n := by exact_mod_cast hn
      have hpt (x : A) :
          (n:ℝ)*(u (x*(b*s))-u x)^2 ≤
          ((n:ℝ)+1)*(u (x*b)-u x)^2+
          (n:ℝ)*((n:ℝ)+1)*(u ((x*b)*s)-u (x*b))^2 := by
        have hsq := sq_nonneg ((u (x*b)-u x)-(n:ℝ)*(u ((x*b)*s)-u (x*b)))
        simp only [mul_assoc] at hsq ⊢
        nlinarith
      have hsum := Finset.sum_le_sum (fun x (_ : x∈S^r) => hpt x)
      simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
      have hp1 : 0≤(n:ℝ)+1 := by positivity
      have hstep := mul_le_mul_of_nonneg_left hbnd hp1
      have hstep' := mul_le_mul_of_nonneg_left hsnd (mul_nonneg hn'.le hp1)
      change _≤((n+1:ℕ):ℝ)^2*E
      push_cast
      nlinarith

omit [Group A] [DecidableEq A] in
lemma finite_variance_identity (F : Finset A) (u : A → ℝ) :
    (∑ x∈F, ∑ y∈F, (u x-u y)^2) =
      2*(F.card:ℝ)*(∑ x∈F, (u x)^2)-2*(∑ x∈F, u x)^2 := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,←Finset.sum_mul,←Finset.mul_sum,nsmul_eq_mul]
  ring

theorem word_ball_poincare (S : Finset A) (h1 : (1:A)∈S)
    (hinv : S⁻¹=S) (u : A → ℝ) (r : ℕ)
    (hu : (∑ x∈S^r, u x)=0) :
    (((S^r).card:ℝ)*(∑ x∈S^r, (u x)^2)) ≤
      2*(r:ℝ)^2*((S^(2*r)).card:ℝ)*energy S (S^(3*r)) u := by
  have hpair (x : A) (hx : x∈S^r) :
      (∑ y∈S^r, (u x-u y)^2) ≤
        ∑ a∈S^(2*r), (u (x*a)-u x)^2 := by
    let F := (S^r).image (fun y => x⁻¹*y)
    have hF : F⊆S^(2*r) := by
      intro a ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
      have hxi : x⁻¹∈S^r := by
        have hh : x⁻¹∈(S^r)⁻¹ := Finset.inv_mem_inv hx
        simpa [←inv_pow,hinv] using hh
      rw [show 2*r=r+r by omega,pow_add]
      exact Finset.mem_mul.mpr ⟨x⁻¹,hxi,y,hy,rfl⟩
    calc
      _ = ∑ a∈F, (u (x*a)-u x)^2 := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro y _
          simp only [mul_inv_cancel_left]
          ring
        · intro y _ z _ h
          exact mul_left_cancel h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hF (by intros; positivity)
  have hsum := Finset.sum_le_sum hpair
  rw [finite_variance_identity,hu,pow_two,zero_mul,mul_zero,sub_zero,Finset.sum_comm] at hsum
  have hw := Finset.sum_le_sum (fun a (ha : a∈S^(2*r)) =>
    word_difference_energy S h1 u r (2*r) a ha)
  simp only [Finset.sum_const,nsmul_eq_mul] at hw
  rw [show r+2*r=3*r by omega] at hw
  have he : 2*((S^r).card:ℝ)*(∑ x∈S^r, (u x)^2)≤
      ((S^(2*r)).card:ℝ)*(2*(r:ℝ))^2*energy S (S^(3*r)) u := by
    have hh := hsum.trans hw
    push_cast at hh
    nlinarith
  nlinarith

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_HarmonicEnergy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_HarmonicFunctionSpace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_CayleyCaccioppoli
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

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

omit [Group A] in
lemma sum_subtype_pair (F : Finset A) (f : A → A → ℝ) :
    (∑ x:F, ∑ y:F, f x.val y.val)=∑ x∈F, ∑ y∈F, f x y := by
  simp only [Finset.sum_coe_sort]
  exact Finset.sum_coe_sort F (fun x => ∑ y∈F, f x y)

lemma sum_neighbor_rows (S F : Finset A) (x : A) (f : A → ℝ)
    (hF : ∀ s∈S, x*s∈F) :
    (∑ y∈F, if x⁻¹*y∈S then f y else 0) = ∑ s∈S, f (x*s) := by
  have he : F.filter (fun y => x⁻¹*y∈S)=S.image (fun s => x*s) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨hy,hs⟩
      exact ⟨x⁻¹*y,hs,mul_inv_cancel_left x y⟩
    · rintro ⟨s,hs,rfl⟩
      exact ⟨hF s hs,by simpa⟩
  rw [←Finset.sum_filter,he,Finset.sum_image]
  intro a _ b _ h
  exact mul_left_cancel h

lemma sum_neighbor_rows_le (S F : Finset A) (x : A) (f : A → ℝ)
    (hf : ∀ y, 0≤f y) :
    (∑ y∈F, if x⁻¹*y∈S then f y else 0) ≤ ∑ s∈S, f (x*s) := by
  have he : F.filter (fun y => x⁻¹*y∈S)⊆S.image (fun s => x*s) := by
    intro y hy
    exact Finset.mem_image.mpr ⟨x⁻¹*y,(Finset.mem_filter.mp hy).2,mul_inv_cancel_left x y⟩
  rw [←Finset.sum_filter]
  calc
    _ ≤ ∑ y∈S.image (fun s => x*s), f y :=
      Finset.sum_le_sum_of_subset_of_nonneg he (by intros; apply hf)
    _ = _ := Finset.sum_image (fun a _ b _ h => mul_left_cancel h)

namespace WordGeometry
variable (W : WordGeometry A)

lemma inv_mem_generators_iff (s : A) : s⁻¹∈W.generators ↔ s∈W.generators := by
  constructor
  · intro hs
    have hh := Finset.inv_mem_inv hs
    simpa only [W.inv_eq,inv_inv] using hh
  · intro hs
    have hh := Finset.inv_mem_inv hs
    simpa only [W.inv_eq] using hh

lemma neighbor_symm (x y : A) : x⁻¹*y∈W.generators ↔ y⁻¹*x∈W.generators := by
  have hh := W.inv_mem_generators_iff (x⁻¹*y)
  simpa only [mul_inv_rev,inv_inv] using hh.symm

lemma cutoff_neighbor_mem_ball (R : ℕ) {x : A} (hx : W.cutoff R x≠0)
    {s : A} (hs : s∈W.generators) : x*s∈W.ball (2*R+1) := by
  apply W.length_le_iff.mp
  have hlen := W.cutoff_ne_zero_length R hx
  have hh := (W.length_mul_generator hs x).1
  omega

theorem caccioppoli (u : A → ℝ) (hu : W.IsHarmonic u) (R : ℕ) :
    (R:ℝ)^2*energy W.generators (W.ball R) u ≤
      4*(W.generators.card:ℝ)*squareMass (W.ball (2*R+1)) u := by
  let F := W.ball (2*R+1)
  let w : F → F → ℝ := fun x y => if x.val⁻¹*y.val∈W.generators then 1 else 0
  let η : F → ℝ := fun x => W.cutoff R x.val
  have hw (x y : F) : w x y=w y x := by
    dsimp [w]
    simp only [W.neighbor_symm x.val y.val]
  have hw0 (x y : F) : 0≤w x y := by dsimp [w]; split <;> positivity
  have hh (x : F) : η x=0 ∨ (∑ y:F, w x y*(u x.val-u y.val))=0 := by
    by_cases hx : η x=0
    · exact Or.inl hx
    right
    have hx' : W.cutoff R x.val≠0 := hx
    simp only [w,ite_mul,one_mul,zero_mul]
    rw [Finset.sum_coe_sort F (fun y : A =>
      if x.val⁻¹*y∈W.generators then u x.val-u y else 0)]
    rw [sum_neighbor_rows W.generators F x.val (fun y => u x.val-u y)
      (fun s hs => W.cutoff_neighbor_mem_ball R hx' hs)]
    exact hu x.val
  have hc := finite_caccioppoli w hw hw0 (fun x:F => u x.val) η hh
  have hL : (R:ℝ)^2*energy W.generators (W.ball R) u ≤
      ∑ x:F, ∑ y:F, w x y*(η x)^2*(u x.val-u y.val)^2 := by
    simp only [w,η,ite_mul,one_mul,zero_mul]
    rw [show (∑ x:F, ∑ y:F, if x.val⁻¹*y.val∈W.generators then
      (W.cutoff R x.val)^2*(u x.val-u y.val)^2 else 0) =
      ∑ x∈F, ∑ y∈F, if x⁻¹*y∈W.generators then
      (W.cutoff R x)^2*(u x-u y)^2 else 0 from
      sum_subtype_pair F (fun x y => if x⁻¹*y∈W.generators then
        (W.cutoff R x)^2*(u x-u y)^2 else 0)]
    have hsub : W.ball R⊆F := W.ball_mono (by omega)
    calc
      _ = ∑ x∈W.ball R, (R:ℝ)^2*(∑ s∈W.generators, (u x-u (x*s))^2) := by
        unfold energy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ ≤ ∑ x∈W.ball R, (W.cutoff R x)^2*(∑ s∈W.generators, (u x-u (x*s))^2) := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_right
        · exact sq_le_sq₀ (by positivity) (W.cutoff_nonneg R x) |>.mpr (W.cutoff_large R hx)
        · exact Finset.sum_nonneg (fun s _ => sq_nonneg _)
      _ = ∑ x∈W.ball R, ∑ y∈F,
          if x⁻¹*y∈W.generators then (W.cutoff R x)^2*(u x-u y)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [sum_neighbor_rows]
        · exact Finset.mul_sum _ _ _
        · intro s hs
          apply W.length_le_iff.mp
          have hlx := W.length_le_iff.mpr hx
          have hhx := (W.length_mul_generator hs x).1
          omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro x hx hxn
        exact Finset.sum_nonneg (fun y hy => by split <;> positivity))
  have hU : (∑ x:F, ∑ y:F, w x y*(u x.val)^2*(η x-η y)^2) ≤
      (W.generators.card:ℝ)*squareMass F u := by
    simp only [w,η,ite_mul,one_mul,zero_mul]
    rw [show (∑ x:F, ∑ y:F, if x.val⁻¹*y.val∈W.generators then
      (u x.val)^2*(W.cutoff R x.val-W.cutoff R y.val)^2 else 0) =
      ∑ x∈F, ∑ y∈F, if x⁻¹*y∈W.generators then
      (u x)^2*(W.cutoff R x-W.cutoff R y)^2 else 0 from
      sum_subtype_pair F (fun x y => if x⁻¹*y∈W.generators then
        (u x)^2*(W.cutoff R x-W.cutoff R y)^2 else 0)]
    unfold squareMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    calc
      _ ≤ ∑ y∈F, if x⁻¹*y∈W.generators then (u x)^2 else 0 := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hs : x⁻¹*y∈W.generators
        · simp only [ite_eq_left hs]
          have ha := W.cutoff_lipschitz_generator R hs x
          simp only [mul_inv_cancel_left,abs_sub_comm] at ha
          have hsquare := (sq_le_one_iff_abs_le_one _).mpr ha
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hsquare (sq_nonneg (u x))
        · simp only [ite_eq_right hs,le_refl]
      _ ≤ ∑ s∈W.generators, (u x)^2 := sum_neighbor_rows_le _ _ _ _ (by intro y; positivity)
      _ = _ := by simp
  have hU' := mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤4)
  change _≤4*(W.generators.card:ℝ)*squareMass F u
  calc
    _ ≤ _ := hL.trans hc
    _ ≤ _ := by simpa only [mul_assoc] using hU'

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_LazyWalkHilbert
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

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

lemma regular_inner (a : A) (f g : RegularHilbert A) :
    inner ℝ (regular a f) g=inner ℝ f (regular a⁻¹ g) := by
  have h := (regular a).inner_map_map f (regular a⁻¹ g)
  simpa only [←regular_mul,mul_inv_cancel,regular_one] using h

namespace WordGeometry
variable (W : WordGeometry A)

lemma generators_card_pos : 0 < W.generators.card :=
  Finset.card_pos.mpr ⟨1,W.one_mem⟩

lemma walkAverage_apply (f : RegularHilbert A) :
    W.walkAverage f = (W.generators.card:ℝ)⁻¹ • ∑ s∈W.generators, regular s f := by
  simp [walkAverage,LinearMap.sum_apply]

lemma lazyWalk_apply (f : RegularHilbert A) :
    W.lazyWalk f = (1/2:ℝ) • (f+W.walkAverage f) := rfl

lemma walkAverage_norm_le (f : RegularHilbert A) : ‖W.walkAverage f‖≤‖f‖ := by
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  rw [W.walkAverage_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
  calc
    _ ≤ (W.generators.card:ℝ)⁻¹ * ∑ s∈W.generators, ‖regular s f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
    _ = ‖f‖ := by simp [hc.ne']

lemma walkAverage_symmetric (f g : RegularHilbert A) :
    inner ℝ (W.walkAverage f) g=inner ℝ f (W.walkAverage g) := by
  simp only [W.walkAverage_apply,real_inner_smul_left,real_inner_smul_right,sum_inner,inner_sum]
  congr 1
  simp only [regular_inner]
  apply Finset.sum_bij (fun s _ => s⁻¹)
  · intro s hs
    rw [←W.inv_eq]
    exact Finset.inv_mem_inv hs
  · intro a _ b _ h; exact inv_injective h
  · intro b hb
    refine ⟨b⁻¹, ?_, inv_inv b⟩
    rw [←W.inv_eq]
    exact Finset.inv_mem_inv hb
  · intro s hs; rfl

lemma lazyWalk_symmetric (f g : RegularHilbert A) :
    inner ℝ (W.lazyWalk f) g=inner ℝ f (W.lazyWalk g) := by
  simp only [W.lazyWalk_apply,real_inner_smul_left,real_inner_smul_right,
    inner_add_left,inner_add_right,W.walkAverage_symmetric]

lemma lazyWalk_norm_le (f : RegularHilbert A) : ‖W.lazyWalk f‖≤‖f‖ := by
  rw [W.lazyWalk_apply,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have ht := norm_add_le f (W.walkAverage f)
  have ha := W.walkAverage_norm_le f
  linarith

lemma lazyWalk_positive (f : RegularHilbert A) : 0 ≤ inner ℝ f (W.lazyWalk f) := by
  have hb := abs_real_inner_le_norm f (W.walkAverage f)
  have h := mul_le_mul_of_nonneg_left (W.walkAverage_norm_le f) (norm_nonneg f)
  have hl := (abs_le.mp (hb.trans h)).1
  simp only [W.lazyWalk_apply,real_inner_smul_right,inner_add_right,
    real_inner_self_eq_norm_sq]
  nlinarith

lemma walkEnergy_nonneg (f : RegularHilbert A) : 0≤W.walkEnergy f := by
  have hb := real_inner_le_norm f (W.lazyWalk f)
  have h := mul_le_mul_of_nonneg_left (W.lazyWalk_norm_le f) (norm_nonneg f)
  unfold walkEnergy
  rw [inner_sub_right,real_inner_self_eq_norm_sq]
  nlinarith

lemma walkEnergy_dissipation (f : RegularHilbert A) :
    ‖f-W.lazyWalk f‖^2 ≤ W.walkEnergy f-W.walkEnergy (W.lazyWalk f) := by
  have hp := W.lazyWalk_positive (f-W.lazyWalk f)
  rw [map_sub] at hp
  simp only [inner_sub_left,inner_sub_right] at hp
  rw [←W.lazyWalk_symmetric f (W.lazyWalk f)] at hp
  have hcomm : inner ℝ (W.lazyWalk f) f = inner ℝ f (W.lazyWalk f) := real_inner_comm _ _
  unfold walkEnergy
  simp only [inner_sub_right,real_inner_self_eq_norm_sq,norm_sub_sq_real]
  nlinarith [real_inner_self_eq_norm_sq (W.lazyWalk f)]

lemma walkEnergy_gradient (f : RegularHilbert A) :
    (∑ s∈W.generators, ‖regular s f-f‖^2) =
      4*(W.generators.card:ℝ)*W.walkEnergy f := by
  have hc : (W.generators.card:ℝ)≠0 := by exact_mod_cast W.generators_card_pos.ne'
  simp only [norm_sub_sq_real,LinearIsometryEquiv.norm_map,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    nsmul_eq_mul,←Finset.mul_sum]
  unfold walkEnergy
  simp only [inner_sub_right,W.lazyWalk_apply,real_inner_smul_right,
    inner_add_right,real_inner_self_eq_norm_sq,W.walkAverage_apply,inner_sum]
  simp_rw [real_inner_comm (regular _ f) f]
  field_simp
  ring

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_LazyWalkProbability
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

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma lazyWalk_coordinate (f : RegularHilbert A) (x : A) :
    W.lazyWalk f x = (1/2:ℝ)*(f x+
      (W.generators.card:ℝ)⁻¹*∑ s∈W.generators, f (s⁻¹*x)) := by
  simp only [W.lazyWalk_apply,W.walkAverage_apply,lp.coeFn_smul,lp.coeFn_add,
    lp.coeFn_sum,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,regular_apply,smul_eq_mul]

lemma lazyWalk_nonnegative (f : RegularHilbert A) (hf : ∀ x, 0≤f x) :
    ∀ x, 0≤W.lazyWalk f x := by
  intro x
  rw [W.lazyWalk_coordinate]
  exact mul_nonneg (by norm_num) (add_nonneg (hf x)
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => hf _))))

lemma lazyWalk_mass (f : RegularHilbert A) (m : ℝ) (hf : HasSum (fun x => f x) m) :
    HasSum (fun x => W.lazyWalk f x) m := by
  have hs : HasSum (fun x => ∑ s∈W.generators, f (s⁻¹*x))
      ((W.generators.card:ℝ)*m) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,Function.comp_apply,Equiv.coe_mulLeft] using
      hasSum_sum (s := W.generators) (fun s _ =>
        (Equiv.mulLeft s⁻¹).hasSum_iff.mpr hf)
  have hc : (W.generators.card:ℝ)≠0 := by exact_mod_cast W.generators_card_pos.ne'
  have hh := HasSum.mul_left (1/2:ℝ) (hf.add (HasSum.mul_left (W.generators.card:ℝ)⁻¹ hs))
  have he : (1/2:ℝ)*(m+(W.generators.card:ℝ)⁻¹*((W.generators.card:ℝ)*m))=m := by
    field_simp; ring
  rw [he] at hh
  simpa only [W.lazyWalk_coordinate] using hh

lemma walkState_succ (n : ℕ) : W.walkState (n+1)=W.lazyWalk (W.walkState n) := by
  simp only [walkState,pow_succ',Module.End.mul_apply]

lemma walkState_nonnegative (n : ℕ) : ∀ x, 0≤W.walkState n x := by
  induction n with
  | zero => intro x; simp only [walkState_zero,lp.single_apply,Pi.single_apply]; split <;> norm_num
  | succ n ih => rw [W.walkState_succ]; exact W.lazyWalk_nonnegative _ ih

lemma walkState_mass (n : ℕ) : HasSum (fun x => W.walkState n x) 1 := by
  induction n with
  | zero =>
    simpa only [walkState_zero,lp.single_apply,Pi.single_apply] using hasSum_ite_eq (1:A) (1:ℝ)
  | succ n ih => rw [W.walkState_succ]; exact W.lazyWalk_mass _ _ ih

lemma walkState_one_pos (n : ℕ) : 0<W.walkState n 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate]
    have hs : 0≤(W.generators.card:ℝ)⁻¹*∑ s∈W.generators, W.walkState n (s⁻¹*1) := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun s _ => W.walkState_nonnegative n _)
    positivity

lemma walkState_support (n : ℕ) {x : A} (hx : x∉W.ball n) : W.walkState n x=0 := by
  induction n generalizing x with
  | zero =>
    have hh : x≠1 := by simpa [ball] using hx
    simp [hh]
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate]
    have hxn : x∉W.ball n := fun h => hx (W.ball_mono (by omega) h)
    rw [ih hxn]
    have hs : (∑ s∈W.generators, W.walkState n (s⁻¹*x))=0 := by
      apply Finset.sum_eq_zero
      intro s hs
      apply ih
      intro h
      apply hx
      change x∈W.generators^(n+1)
      rw [pow_succ']
      exact Finset.mem_mul.mpr ⟨s,hs,s⁻¹*x,h,mul_inv_cancel_left s x⟩
    rw [hs]; ring

lemma walkPower_symmetric (n : ℕ) (f g : RegularHilbert A) :
    inner ℝ ((W.lazyWalk^n) f) g=inner ℝ f ((W.lazyWalk^n) g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    calc
      _ = inner ℝ ((W.lazyWalk^n) (W.lazyWalk f)) g := by
        rw [pow_succ,Module.End.mul_apply]
      _ = inner ℝ (W.lazyWalk f) ((W.lazyWalk^n) g) := ih _ _
      _ = inner ℝ f (W.lazyWalk ((W.lazyWalk^n) g)) := W.lazyWalk_symmetric _ _
      _ = _ := by rw [pow_succ',Module.End.mul_apply]

lemma walkState_double_at_one (n : ℕ) : W.walkState (2*n) 1=‖W.walkState n‖^2 := by
  have hh := W.walkPower_symmetric n (lp.single 2 (1:A) (1:ℝ)) (W.walkState n)
  rw [lp.inner_single_left] at hh
  have he : (W.lazyWalk^n) (W.walkState n)=W.walkState (2*n) := by
    simp only [walkState,←Module.End.mul_apply,←pow_add,two_mul]
  rw [he] at hh
  change inner ℝ (W.walkState n) (W.walkState n) = inner ℝ 1 (W.walkState (2*n) 1) at hh
  simpa only [real_inner_self_eq_norm_sq,Real.inner_apply,one_mul] using hh.symm

lemma walkState_norm_sq (n : ℕ) :
    ‖W.walkState n‖^2=∑ x∈W.ball n, (W.walkState n x)^2 := by
  rw [←real_inner_self_eq_norm_sq]
  change (∑' x : A, inner ℝ (W.walkState n x) (W.walkState n x))=_
  simp only [Real.inner_apply]
  rw [tsum_eq_sum (s := W.ball n)]
  · apply Finset.sum_congr rfl; intro x _; ring
  · intro x hx; rw [W.walkState_support n hx]; simp

lemma walkState_norm_lower (n : ℕ) :
    1≤((W.ball n).card:ℝ)*‖W.walkState n‖^2 := by
  have hmass : (∑ x∈W.ball n, W.walkState n x)=1 := by
    rw [←(W.walkState_mass n).tsum_eq]
    exact (tsum_eq_sum (f := fun x => W.walkState n x) (s := W.ball n)
      (fun x hx => W.walkState_support n (x := x) hx)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (W.ball n) (fun _ => (1:ℝ))
    (fun x => W.walkState n x)
  simpa only [one_mul,hmass,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,
    ←W.walkState_norm_sq] using hcs

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_WalkEnergyLower
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

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma exists_word_ball_boundary [Infinite A] (r : ℕ) :
    ∃ a∈W.ball (r+1), a∉W.ball r := by
  by_contra! hbad
  have he : W.ball (r+1)=W.ball r :=
    Finset.Subset.antisymm hbad (W.ball_mono (by omega))
  have hs : ∀ n, W.ball n⊆W.ball r := by
    intro n
    induction n with
    | zero =>
      apply W.ball_mono
      omega
    | succ n ih =>
      change W.generators^(n+1)⊆W.ball r
      rw [pow_succ]
      have hh := Finset.mul_subset_mul ih (Finset.Subset.refl W.generators)
      exact hh.trans (by simpa only [ball,←pow_succ] using he.le)
  have hfinite : (Set.univ:Set A).Finite := (W.ball r).finite_toSet.subset (by
    intro a _
    obtain ⟨n,hn⟩ := W.exists_mem_ball a
    exact hs n hn)
  exact Set.infinite_univ hfinite

lemma regular_word_displacement (f : RegularHilbert A) (C : ℝ)
    (hgen : ∀ s∈W.generators, ‖regular s f-f‖≤C) (r : ℕ)
    {a : A} (ha : a∈W.ball r) : ‖regular a f-f‖≤(r:ℝ)*C := by
  induction r generalizing a with
  | zero =>
    have he : a=1 := by simpa [ball] using ha
    simp [he]
  | succ r ih =>
    change a∈W.generators^(r+1) at ha
    rw [pow_succ] at ha
    obtain ⟨b,hb,s,hs,rfl⟩ := Finset.mem_mul.mp ha
    have he : regular (b*s) f-f = regular b (regular s f-f)+(regular b f-f) := by
      rw [regular_mul,map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖regular b (regular s f-f)‖+‖regular b f-f‖ := norm_add_le _ _
      _ = ‖regular s f-f‖+‖regular b f-f‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ C+(r:ℝ)*C := add_le_add (hgen s hs) (ih hb)
      _ = _ := by push_cast; ring

lemma regular_energy_displacement (f : RegularHilbert A) (r : ℕ)
    {a : A} (ha : a∈W.ball r) :
    ‖regular a f-f‖≤(r:ℝ)*Real.sqrt (4*(W.generators.card:ℝ)*W.walkEnergy f) := by
  apply W.regular_word_displacement f _ ?_ r ha
  intro s hs
  have h := (Finset.single_le_sum (f := fun t => ‖regular t f-f‖^2)
    (fun _ _ => sq_nonneg _) hs).trans_eq (W.walkEnergy_gradient f)
  have he : 0≤4*(W.generators.card:ℝ)*W.walkEnergy f := by
    exact mul_nonneg (by positivity) (W.walkEnergy_nonneg f)
  have hsqrt := Real.sq_sqrt he
  nlinarith [norm_nonneg (regular s f-f),Real.sqrt_nonneg (4*(W.generators.card:ℝ)*W.walkEnergy f)]

lemma supported_energy_bound [Infinite A] (r : ℕ) (f : RegularHilbert A)
    (hsupp : ∀ a∉W.ball r, f a=0) :
    f 1^2≤(r+1:ℝ)^2*4*(W.generators.card:ℝ)*W.walkEnergy f := by
  obtain ⟨a,ha,ha'⟩ := W.exists_word_ball_boundary r
  have hai : a⁻¹∉W.ball r := by
    intro hh
    have hi := Finset.inv_mem_inv hh
    apply ha'
    simpa only [ball,←inv_pow,W.inv_eq,inv_inv] using hi
  have hp := lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) (regular a f-f) 1
  have hb := W.regular_energy_displacement f (r+1) ha
  have hv : ‖(regular a f-f) 1‖=|f 1| := by
    simp only [lp.coeFn_sub,Pi.sub_apply,regular_apply,mul_one,hsupp a⁻¹ hai,
      zero_sub,norm_neg,Real.norm_eq_abs]
  rw [hv] at hp
  have h := hp.trans hb
  have ht := pow_le_pow_left₀ (abs_nonneg (f 1)) h 2
  have he : 0≤4*(W.generators.card:ℝ)*W.walkEnergy f :=
    mul_nonneg (by positivity) (W.walkEnergy_nonneg f)
  rw [mul_pow,Real.sq_sqrt he,sq_abs] at ht
  push_cast at ht
  nlinarith

lemma walkState_energy_pos [Infinite A] (n : ℕ) : 0<W.walkEnergy (W.walkState n) := by
  have hp := W.walkState_one_pos n
  have hb := W.supported_energy_bound n (W.walkState n) (fun _ ha => W.walkState_support n ha)
  have hn := W.walkEnergy_nonneg (W.walkState n)
  by_contra! h
  have he : W.walkEnergy (W.walkState n)=0 := le_antisymm h hn
  rw [he,mul_zero] at hb
  nlinarith

lemma walkState_energy_lower [Infinite A] (n : ℕ) :
    1≤((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.generators.card:ℝ)*
      W.walkEnergy (W.walkState (2*n)) := by
  have hn := W.walkState_norm_lower n
  have hb := W.supported_energy_bound (2*n) (W.walkState (2*n))
    (fun _ ha => W.walkState_support _ ha)
  rw [W.walkState_double_at_one] at hb
  have hsq : 1≤((W.ball n).card:ℝ)^2*(‖W.walkState n‖^2)^2 := by
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hn]
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ((W.ball n).card:ℝ))
  push_cast at hh
  nlinarith

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_ProjectedWalkFunctions
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

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma exists_large_generator_gradient (f : RegularHilbert A) :
    ∃ t∈W.generators, 4*W.walkEnergy f≤‖regular t f-f‖^2 := by
  by_contra! h
  have hh := Finset.sum_lt_sum_of_nonempty (show W.generators.Nonempty from ⟨1,W.one_mem⟩)
    (fun s hs => h s hs)
  rw [W.walkEnergy_gradient] at hh
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  nlinarith

lemma projectedFunction_one (f : RegularHilbert A) (t : A) :
    W.projectedFunction f t 1=0 := by simp [projectedFunction]

lemma projectedFunction_edge_bound (f : RegularHilbert A) (hf : 0<W.walkEnergy f)
    (t : A) (ht : t∈W.generators) (x s : A) (hs : s∈W.generators) :
    |W.projectedFunction f t (x*s)-W.projectedFunction f t x|≤1 := by
  let q := 4*(W.generators.card:ℝ)*W.walkEnergy f
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hq : 0<q := mul_pos (mul_pos (by norm_num) hc) hf
  have hg (a : A) (ha : a∈W.generators) : ‖regular a f-f‖≤Real.sqrt q := by
    have h := W.regular_energy_displacement f 1 (by simpa [ball] using ha)
    simpa only [Nat.cast_one,one_mul] using h
  have he : (regular (x*s) f-f)-(regular x f-f)=regular x (regular s f-f) := by
    rw [regular_mul,map_sub]
    abel
  unfold projectedFunction
  rw [←sub_div,←inner_sub_left,he,abs_div,abs_of_pos hq]
  apply (div_le_one hq).mpr
  calc
    _ ≤ ‖regular x (regular s f-f)‖*‖regular t f-f‖ := abs_real_inner_le_norm _ _
    _ = ‖regular s f-f‖*‖regular t f-f‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ Real.sqrt q*Real.sqrt q := mul_le_mul (hg s hs) (hg t ht) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = q := Real.mul_self_sqrt hq.le

lemma projectedFunction_length_bound (f : RegularHilbert A) (hf : 0<W.walkEnergy f)
    (t : A) (ht : t∈W.generators) (x : A) :
    |W.projectedFunction f t x|≤(W.length x:ℝ) := by
  let q := 4*(W.generators.card:ℝ)*W.walkEnergy f
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hq : 0<q := mul_pos (mul_pos (by norm_num) hc) hf
  have hx := W.regular_energy_displacement f (W.length x) (W.mem_ball_length x)
  have ht' := W.regular_energy_displacement f 1 (by simpa [ball] using ht)
  simp only [Nat.cast_one,one_mul] at ht'
  unfold projectedFunction
  rw [abs_div,abs_of_pos hq]
  apply (div_le_iff₀ hq).mpr
  calc
    _ ≤ ‖regular x f-f‖*‖regular t f-f‖ := abs_real_inner_le_norm _ _
    _ ≤ ((W.length x:ℝ)*Real.sqrt q)*Real.sqrt q :=
      mul_le_mul hx ht' (norm_nonneg _) (by positivity)
    _ = (W.length x:ℝ)*q := by rw [mul_assoc,Real.mul_self_sqrt hq.le]

lemma projectedFunction_generator_lower (f : RegularHilbert A) (hf : 0<W.walkEnergy f)
    (t : A) (ht : 4*W.walkEnergy f≤‖regular t f-f‖^2) :
    (W.generators.card:ℝ)⁻¹≤W.projectedFunction f t t := by
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hq : 0<4*(W.generators.card:ℝ)*W.walkEnergy f := by positivity
  unfold projectedFunction
  rw [real_inner_self_eq_norm_sq]
  apply (le_div_iff₀ hq).mpr
  have he : (W.generators.card:ℝ)⁻¹*(4*(W.generators.card:ℝ)*W.walkEnergy f)=4*W.walkEnergy f := by
    field_simp
  rw [he]
  exact ht

lemma sum_walk_displacement (f : RegularHilbert A) :
    (∑ s∈W.generators, (f-regular s f))=(2*(W.generators.card:ℝ)) • (f-W.lazyWalk f) := by
  have hc : (W.generators.card:ℝ)≠0 := by exact_mod_cast W.generators_card_pos.ne'
  rw [Finset.sum_sub_distrib,Finset.sum_const,←Nat.cast_smul_eq_nsmul ℝ,W.lazyWalk_apply,W.walkAverage_apply]
  simp only [smul_sub,smul_add,smul_smul]
  have h1 : (2*(W.generators.card:ℝ))*(1/2)=W.generators.card := by ring
  have h2 : (2*(W.generators.card:ℝ))*(1/2)*(W.generators.card:ℝ)⁻¹=1 := by field_simp
  rw [h1,←mul_assoc (2*(W.generators.card:ℝ)) (1/2) (W.generators.card:ℝ)⁻¹,h2,one_smul]
  module

lemma projectedFunction_residual (f : RegularHilbert A) (t x : A) :
    (∑ s∈W.generators, (W.projectedFunction f t x-W.projectedFunction f t (x*s)))=
      (2*(W.generators.card:ℝ))* inner ℝ (regular x (f-W.lazyWalk f)) (regular t f-f) /
        (4*(W.generators.card:ℝ)*W.walkEnergy f) := by
  simp only [projectedFunction,←sub_div,←Finset.sum_div,←inner_sub_left,←sum_inner]
  have he : (∑ s∈W.generators, (regular x f-f-(regular (x*s) f-f)))=
      regular x (∑ s∈W.generators, (f-regular s f)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [regular_mul,map_sub]
    abel
  rw [he,W.sum_walk_displacement,map_smul,real_inner_smul_left]

lemma projectedFunction_residual_sq (f : RegularHilbert A) (hf : 0<W.walkEnergy f)
    (t : A) (ht : t∈W.generators) (x : A) :
    (∑ s∈W.generators, (W.projectedFunction f t x-W.projectedFunction f t (x*s)))^2≤
      (W.generators.card:ℝ)*‖f-W.lazyWalk f‖^2/W.walkEnergy f := by
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hgrad := (Finset.single_le_sum (f := fun s => ‖regular s f-f‖^2)
    (fun s hs => sq_nonneg _) ht).trans_eq (W.walkEnergy_gradient f)
  have hi := abs_real_inner_le_norm (regular x (f-W.lazyWalk f)) (regular t f-f)
  rw [LinearIsometryEquiv.norm_map] at hi
  have hisq := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [sq_abs,mul_pow] at hisq
  have hb := mul_le_mul_of_nonneg_left hgrad (sq_nonneg ‖f-W.lazyWalk f‖)
  rw [W.projectedFunction_residual]
  rw [div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos (show 0<4*(W.generators.card:ℝ)*W.walkEnergy f by positivity)) hf).mpr
  have hm := mul_le_mul_of_nonneg_left (hisq.trans hb)
    (show 0≤4*(W.generators.card:ℝ)^2*W.walkEnergy f by positivity)
  nlinarith only [hm]

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_WalkAlmostHarmonic
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

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma walkState_energy_antitone : Antitone (fun n => W.walkEnergy (W.walkState n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := W.walkEnergy_dissipation (W.walkState n)
  rw [←W.walkState_succ] at h
  nlinarith [sq_nonneg ‖W.walkState n-W.lazyWalk (W.walkState n)‖]

lemma walk_energy_inverse_sparse [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    ∃ C : ℝ, 0≤C ∧ ∀ R, ∃ m≥R,
      (W.walkEnergy (W.walkState m))⁻¹≤C*(m:ℝ)^(2*d+2) := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨36*(W.generators.card:ℝ)*(C:ℝ)^2,by positivity,?_⟩
  intro R
  obtain ⟨n,hn,hvol⟩ := hC (max R 1)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hnR : R≤n := (le_max_left R 1).trans hn
  refine ⟨2*n,by omega,?_⟩
  have hV : ((W.ball n).card:ℝ)≤(C:ℝ)*(n:ℝ)^d := by exact_mod_cast hvol
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpoly : ((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.generators.card:ℝ)≤
      (36*(W.generators.card:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2) := by
    calc
      _ ≤ ((C:ℝ)*(n:ℝ)^d)^2*(3*(n:ℝ))^2*4*(W.generators.card:ℝ) := by
        gcongr
        linarith
      _ = (36*(W.generators.card:ℝ)*(C:ℝ)^2)*(n:ℝ)^(2*d+2) := by
        rw [pow_add,pow_mul]
        ring
      _ ≤ _ := by
        gcongr
        linarith
  have hb := W.walkState_energy_lower n
  have hh := mul_le_mul_of_nonneg_right hpoly (W.walkState_energy_pos (2*n)).le
  have hf : 1≤((36*(W.generators.card:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2))*
      W.walkEnergy (W.walkState (2*n)) := hb.trans hh
  exact (inv_le_iff_one_le_mul₀ (W.walkState_energy_pos (2*n))).mpr hf

theorem exists_walk_small_relative_residual [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) (ε : ℝ) (hε : 0<ε) :
    ∃ n, 0<W.walkEnergy (W.walkState n) ∧
      ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2≤ε*W.walkEnergy (W.walkState n) := by
  obtain ⟨C,hC,hpoly⟩ := W.walk_energy_inverse_sparse d hg
  obtain ⟨n,hn⟩ := exists_small_relative_dissipation
    (fun n => W.walkEnergy (W.walkState n))
    (fun n => ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2)
    W.walkState_energy_pos W.walkState_energy_antitone
    (fun n => by simpa only [W.walkState_succ] using W.walkEnergy_dissipation (W.walkState n))
    (2*d+2) C hC hpoly ε hε
  exact ⟨n,W.walkState_energy_pos n,hn⟩

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_AlmostHarmonicCompactness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter
open scoped Classical Pointwise BigOperators Topology

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

include W in
lemma countable_group : Countable A := by
  apply Set.countable_univ_iff.mp
  have hc : (⋃ n:ℕ, (W.ball n:Set A)).Countable :=
    Set.countable_iUnion (fun n => (W.ball n).finite_toSet.countable)
  apply hc.mono
  intro a _
  obtain ⟨n,hn⟩ := W.exists_mem_ball a
  exact Set.mem_iUnion.mpr ⟨n,hn⟩

lemma exists_projected_approximation [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) (δ : ℝ) (hδ : 0<δ) :
    ∃ u : A → ℝ, u 1=0 ∧ (∀ x, |u x|≤(W.length x:ℝ)) ∧
      (∀ x s, s∈W.generators → |u (x*s)-u x|≤1) ∧
      (W.generators.card:ℝ)⁻¹^2≤∑ s∈W.generators, (u s)^2 ∧
      ∀ x, |∑ s∈W.generators, (u x-u (x*s))|≤δ := by
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  obtain ⟨n,hE,hres⟩ := W.exists_walk_small_relative_residual d hg
    (δ^2/(W.generators.card:ℝ)) (div_pos (sq_pos_of_pos hδ) hc)
  let f := W.walkState n
  obtain ⟨t,ht,hlarge⟩ := W.exists_large_generator_gradient f
  let u := W.projectedFunction f t
  have hlow := W.projectedFunction_generator_lower f hE t hlarge
  refine ⟨u,W.projectedFunction_one f t,W.projectedFunction_length_bound f hE t ht,
    W.projectedFunction_edge_bound f hE t ht,?_,?_⟩
  · have hs : (W.generators.card:ℝ)⁻¹^2≤(u t)^2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hc.le) hlow 2
    exact hs.trans (Finset.single_le_sum (fun s hs => sq_nonneg (u s)) ht)
  · intro x
    have h := W.projectedFunction_residual_sq f hE t ht x
    have hb : (W.generators.card:ℝ)*‖f-W.lazyWalk f‖^2/W.walkEnergy f≤δ^2 := by
      apply (div_le_iff₀ hE).mpr
      have hh := mul_le_mul_of_nonneg_left hres hc.le
      have he : (W.generators.card:ℝ)*(δ^2/(W.generators.card:ℝ)*W.walkEnergy f)=δ^2*W.walkEnergy f := by
        field_simp
      rw [he] at hh
      exact hh
    have hh : (∑ s∈W.generators, (u x-u (x*s)))^2≤δ^2 := h.trans hb
    nlinarith [sq_abs (∑ s∈W.generators, (u x-u (x*s))),abs_nonneg (∑ s∈W.generators, (u x-u (x*s)))]

theorem exists_nonconstant_lipschitz_harmonic [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    ∃ u : A → ℝ, W.IsHarmonic u ∧ u 1=0 ∧
      (∀ x, |u x|≤(W.length x:ℝ)) ∧
      (∀ x s, s∈W.generators → |u (x*s)-u x|≤1) ∧
      ∃ s∈W.generators, u s≠0 := by
  let _ : Countable A := W.countable_group
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
  have hu1 : u 1=0 := by
    have hh : Tendsto (fun n => v (φ n) 1) atTop (𝓝 0) := by
      simpa only [hv1] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hxlim 1) hh
  have hbound (x:A) : |u x|≤(W.length x:ℝ) := abs_le.mpr (huK x (Set.mem_univ x))
  have hedge (x s:A) (hs:s∈W.generators) : |u (x*s)-u x|≤1 :=
    le_of_tendsto ((hxlim (x*s)).sub (hxlim x)).abs (Filter.Eventually.of_forall (fun n => hvedge (φ n) x s hs))
  have hgrad : (W.generators.card:ℝ)⁻¹^2≤∑ s∈W.generators, (u s)^2 := by
    have hl := tendsto_finsetSum W.generators (fun s hs => (hxlim s).pow 2)
    exact ge_of_tendsto hl (Filter.Eventually.of_forall (fun n => hvgrad (φ n)))
  have hharm : W.IsHarmonic u := by
    intro x
    have hl := tendsto_finsetSum W.generators (fun s hs => (hxlim x).sub (hxlim (x*s)))
    have hz : Tendsto (fun n : ℕ => 1/((φ n:ℝ)+1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    have hnonneg : (0:ℝ)≤ |∑ s∈W.generators, (u x-u (x*s))| := abs_nonneg _
    have hle : |∑ s∈W.generators, (u x-u (x*s))|≤0 :=
      le_of_tendsto_of_tendsto hl.abs hz (Filter.Eventually.of_forall (fun n => hvres (φ n) x))
    exact abs_eq_zero.mp (le_antisymm hle hnonneg)
  refine ⟨u,hharm,hu1,hbound,hedge,?_⟩
  by_contra! hn
  have hz : (∑ s∈W.generators, (u s)^2)=0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [hn s hs]
    norm_num
  rw [hz] at hgrad
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hp := sq_pos_of_pos (inv_pos.mpr hc)
  linarith

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_CoverPoincare
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

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma squareMass_around (a : A) (r : ℕ) (u : A → ℝ) :
    squareMass (W.around a r) u = squareMass (W.ball r) (fun x => u (a*x)) := by
  unfold squareMass around
  rw [Finset.sum_image]
  intro x _ y _ h
  exact mul_left_cancel h

lemma energy_around (a : A) (r : ℕ) (u : A → ℝ) :
    energy W.generators (W.around a r) u =
      energy W.generators (W.ball r) (fun x => u (a*x)) := by
  unfold energy around
  rw [Finset.sum_image]
  · simp only [mul_assoc]
  · intro x _ y _ h
    exact mul_left_cancel h

lemma sum_around (a : A) (r : ℕ) (u : A → ℝ) :
    (∑ x∈W.around a r, u x) = ∑ y∈W.ball r, u (a*y) := by
  unfold around
  rw [Finset.sum_image]
  intro x _ y _ h
  exact mul_left_cancel h

lemma translated_poincare (a : A) (r K : ℕ) (u : A → ℝ)
    (hvol : (W.ball (7*r)).card≤K*(W.ball r).card)
    (hu : (∑ x∈W.around a (2*r), u x)=0) :
    squareMass (W.around a (2*r)) u ≤
      8*(r:ℝ)^2*(K:ℝ)*energy W.generators (W.around a (6*r)) u := by
  rw [W.sum_around] at hu
  have hp := word_ball_poincare W.generators W.one_mem W.inv_eq
    (fun x => u (a*x)) (2*r) hu
  change ((W.ball (2*r)).card:ℝ)*squareMass (W.ball (2*r)) (fun x => u (a*x)) ≤ _ at hp
  rw [←W.squareMass_around] at hp
  have he : energy W.generators (W.generators^(3*(2*r))) (fun x => u (a*x)) =
      energy W.generators (W.around a (6*r)) u := by
    rw [W.energy_around]
    congr 1
    change W.generators^(3*(2*r))=W.generators^(6*r)
    congr 1; omega
  rw [he] at hp
  have hv : (W.generators^(2*(2*r))).card≤K*(W.ball (2*r)).card := by
    calc
      _ ≤ (W.ball (7*r)).card := Finset.card_le_card (W.ball_mono (by omega))
      _ ≤ _ := hvol.trans (Nat.mul_le_mul_left _ (Finset.card_le_card (W.ball_mono (by omega))))
  have hv' : ((W.generators^(2*(2*r))).card:ℝ)≤(K:ℝ)*((W.ball (2*r)).card:ℝ) := by exact_mod_cast hv
  have hbpos : (0:ℝ)<(W.ball (2*r)).card := by exact_mod_cast W.ball_card_pos (2*r)
  have hepos := energy_nonneg W.generators (W.around a (6*r)) u
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
      8*(r:ℝ)^2*(K:ℝ)^2*energy W.generators (W.ball (R+6*r)) u := by
  have hcover' := sum_le_sum_of_finite_cover J (fun a => W.around a (2*r))
    (W.ball R) hcover (fun x => (u x)^2) (fun x => sq_nonneg _)
  have hpsum := Finset.sum_le_sum (fun a (ha : a∈J) => W.translated_poincare a r K u hvol (hu a ha))
  have hsub : ∀ a∈J, W.around a (6*r)⊆W.ball (R+6*r) :=
    fun a ha => W.around_subset_ball (hJR ha)
  have hover : ∀ x∈W.ball (R+6*r), (J.filter (fun a => x∈W.around a (6*r))).card≤K := by
    intro x _
    apply W.packing_overlap J r (6*r) K hJ
    simpa only [show 6*r+r=7*r by omega] using hvol
  have he := sum_le_sum_of_finite_overlap J (fun a => W.around a (6*r))
    (W.ball (R+6*r)) hsub K hover
    (fun x => ∑ s∈W.generators, (u (x*s)-u x)^2)
    (fun x => Finset.sum_nonneg (fun s _ => sq_nonneg _))
  change (∑ a∈J, energy W.generators (W.around a (6*r)) u)≤
    (K:ℝ)*energy W.generators (W.ball (R+6*r)) u at he
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
      8*(K:ℝ)^2*(W.generators.card:ℝ)*(r:ℝ)^2*squareMass (W.ball (5*R)) u := by
  have hp := W.cover_mass_energy R r K J hJR hJ hcover hvol u hu
  have hem := energy_mono W.generators (W.ball_mono (show R+6*r≤2*R by omega)) u
  have hm := mul_le_mul_of_nonneg_left hem (by positivity : 0≤8*(r:ℝ)^2*(K:ℝ)^2)
  have hp' : squareMass (W.ball R) u≤8*(r:ℝ)^2*(K:ℝ)^2*energy W.generators (W.ball (2*R)) u := hp.trans hm
  have hc := W.caccioppoli u hharm (2*R)
  have hqm := squareMass_mono (W.ball_mono (show 2*(2*R)+1≤5*R by omega)) u
  have hq := mul_le_mul_of_nonneg_left hqm (by positivity : 0≤4*(W.generators.card:ℝ))
  have hc' : (R:ℝ)^2*energy W.generators (W.ball (2*R)) u≤
      (W.generators.card:ℝ)*squareMass (W.ball (5*R)) u := by
    push_cast at hc
    nlinarith
  have hm' := mul_le_mul_of_nonneg_left hp' (sq_nonneg (R:ℝ))
  have hm'' := mul_le_mul_of_nonneg_left hc' (by positivity : 0≤8*(r:ℝ)^2*(K:ℝ)^2)
  nlinarith

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GeneralizedGramSpectrum
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_FunctionGramMatrix
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_PolynomialHarmonicSpace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

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

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GramGrowthScales
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

namespace WordGeometry
variable (W : WordGeometry A)

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

lemma gram_sparse_product_growth (d k : ℕ) (hg : SparseGrowth.HasDegree W.generators d)
    (v : ι → A → ℝ) (hv : ∀ i, W.HasPolynomialGrowth k (v i)) (n₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R, ∃ n≥R,
      ((W.ball (max n n₀)).card:ℝ)^(Fintype.card ι) *
          (functionGram (W.ball (max n n₀)) v).det ≤
        C*(n:ℝ)^((Fintype.card ι)*(2*d+2*k)) := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨M,hM,hvM⟩ := W.finite_family_growth_bound k v hv
  let m := Fintype.card ι
  let D : ℝ := (m.factorial:ℝ)*((C:ℝ)*M^2)^m
  refine ⟨(C:ℝ)^m*D,by dsimp [D]; positivity,?_⟩
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
        (by dsimp [D]; positivity)
    _ = _ := by
      rw [mul_pow,←pow_mul]
      calc
        _ = ((C:ℝ)^m*D)*((n:ℝ)^(d*m)*(n:ℝ)^(m*(d+2*k))) := by ring
        _ = _ := by rw [←pow_add]; congr 2; ring

theorem function_gram_paired_scales (d k : ℕ) (hg : SparseGrowth.HasDegree W.generators d)
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

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_MatrixLowGrowthSubspace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_HarmonicDimensionBound
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical Pointwise BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A ι : Type*} [Group A] [Fintype ι] (W : WordGeometry A)

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

theorem harmonic_independent_card_bound (d k : ℕ) (hg : SparseGrowth.HasDegree W.generators d)
    (v : ι → A → ℝ) (hharm : ∀ i, W.IsHarmonic (v i))
    (hpol : ∀ i, W.HasPolynomialGrowth k (v i)) (hli : LinearIndependent ℝ v)
    (L : ℕ) (hL : 0 < L)
    (hgap : 8*(10^(4*(2*d+2*k+1)))^4*W.generators.card < 10^(4*L)) :
    Fintype.card ι ≤ 2*(10^(4*(2*d+2*k+1)))^L := by
  by_cases hm : Fintype.card ι=0
  · simp only [hm]; positivity
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
  have hstrict := scale_ratio_strict K W.generators.card L r R hr hscale hgap
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
    have hc := W.harmonic_cover_kernel_bound R r K hR hrR J hJR hJ hcover hvol
      (functionCombination v a.val) (W.harmonic_functionCombination v hharm _) havg
    have hl := hVratio a.val a.property
    rw [functionGram_quadratic,functionGram_quadratic] at hl
    have hm := mul_le_mul_of_nonneg_left hl
      (by positivity : 0 ≤ 8*(K:ℝ)^2*(W.generators.card:ℝ)*(r:ℝ)^2)
    have hlow := mul_lt_mul_of_pos_right hstrict hQ
    nlinarith
  have hdim : Module.finrank ℝ V ≤ J.card := by
    have hh := LinearMap.finrank_le_finrank_of_injective hInjective
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using hh
  exact hVdim.trans (Nat.mul_le_mul_left 2 (hdim.trans hJbound))

omit [Fintype ι] in

theorem polynomialHarmonicSpace_finiteDimensional (d k : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    FiniteDimensional ℝ (W.polynomialHarmonicSpace k) := by
  let K : ℕ := 10^(4*(2*d+2*k+1))
  let L : ℕ := 8*K^4*W.generators.card+1
  have hL : 0 < L := by dsimp [L]; omega
  have hgap : 8*K^4*W.generators.card < 10^(4*L) := by
    have hpow : L < 10^L := L.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (by omega) L)
    have hm : 10^L ≤ 10^(4*L) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (by dsimp [L]; omega : 8*K^4*W.generators.card < L).trans (hpow.trans_le hm)
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

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_HarmonicLinearQuotient
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

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
universe u
variable {A : Type u} [Group A] (W : WordGeometry A)

lemma harmonic_constant_of_attained_max {u : A → ℝ} (hu : W.IsHarmonic u)
    (a : A) (hmax : ∀ x, u x≤u a) : ∀ x, u x=u a := by
  have hstep (x : A) (hx : u x=u a) (s : A) (hs : s∈W.generators) : u (x*s)=u a := by
    have hn (t:A) (ht:t∈W.generators) : 0≤u x-u (x*t) := by rw [hx]; exact sub_nonneg.mpr (hmax _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hn).mp (hu x) s hs
    linarith
  have hball (n:ℕ) : ∀ b∈W.ball n, u (a*b)=u a := by
    induction n with
    | zero =>
      intro b hb
      have he : b=1 := by simpa [ball] using hb
      simp [he]
    | succ n ih =>
      intro b hb
      change b∈W.generators^(n+1) at hb
      rw [pow_succ] at hb
      obtain ⟨c,hc,s,hs,rfl⟩ := Finset.mem_mul.mp hb
      simpa only [mul_assoc] using hstep (a*c) (ih c hc) s hs
  intro x
  obtain ⟨n,hn⟩ := W.exists_mem_ball (a⁻¹*x)
  simpa using hball n (a⁻¹*x) hn

lemma harmonic_constant_of_finite_range {u : A → ℝ} (hu : W.IsHarmonic u)
    (hf : (Set.range u).Finite) : ∀ x, u x=u 1 := by
  obtain ⟨m,⟨a,rfl⟩,hm⟩ := Set.exists_max_image (Set.range u) id hf (Set.range_nonempty u)
  have he := W.harmonic_constant_of_attained_max hu a (fun x => hm (u x) ⟨x,rfl⟩)
  intro x
  exact (he x).trans (he 1).symm

lemma finite_range_of_finite_harmonic_image (k : ℕ)
    (hf : (Set.range (W.harmonicRepresentation k)).Finite) (u : W.polynomialHarmonicSpace k) :
    (Set.range (u:A → ℝ)).Finite := by
  apply (hf.image (fun e => (e u:A → ℝ) 1)).subset
  rintro y ⟨x,rfl⟩
  refine ⟨W.harmonicRepresentation k x⁻¹,⟨x⁻¹,rfl⟩,?_⟩
  change (u:A → ℝ) ((x⁻¹)⁻¹*1)=(u:A → ℝ) x
  simp

lemma infinite_harmonic_linear_image [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    (Set.range (W.harmonicRepresentation 1)).Infinite := by
  obtain ⟨u,hu,hu1,hbound,hedge,s,hs,hne⟩ := W.exists_nonconstant_lipschitz_harmonic d hg
  have hupol : W.HasPolynomialGrowth 1 u := by
    apply (W.polynomial_growth_iff_length 1 u).mpr
    refine ⟨1,by norm_num,?_⟩
    intro x
    simpa only [pow_one,one_mul] using (hbound x).trans (by linarith : (W.length x:ℝ)≤(W.length x:ℝ)+1)
  let v : W.polynomialHarmonicSpace 1 := ⟨u,hu,hupol⟩
  intro hf
  have hconst := W.harmonic_constant_of_finite_range hu (W.finite_range_of_finite_harmonic_image 1 hf v)
  exact hne ((hconst s).trans hu1)

theorem exists_infinite_finiteDimensional_linear_image_bs_oai [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V),
      FiniteDimensional ℝ V ∧ ∃ ρ : A →* (V ≃ₗ[ℝ] V), (Set.range ρ).Infinite := by
  refine ⟨W.polynomialHarmonicSpace 1,inferInstance,inferInstance,?_,W.harmonicRepresentation 1,
    W.infinite_harmonic_linear_image d hg⟩
  exact W.polynomialHarmonicSpace_finiteDimensional d 1 hg

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image_bs_oai.{u} := @OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image_bs_oai.{u}
