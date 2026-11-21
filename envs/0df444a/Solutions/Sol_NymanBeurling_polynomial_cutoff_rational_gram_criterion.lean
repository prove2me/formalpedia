-- Prove2me | solution 1 for NymanBeurling.polynomial_cutoff_rational_gram_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:53:17.897978+00:00
-- url     : https://prove2.me/submissions/4e955794-a7e6-40b9-a1ff-3a3ccf8940df

import Definitions.Def_NymanBeurling_RationalGram

open Finset
open NymanBeurling.RationalGram
set_option maxHeartbeats 1600000
namespace RationalGramProof
-- Finite differences and divisor inversion from the accepted proof of
-- NymanBeurling.certificate_moebius_coefficients_and_quadratic_cutoff.
private lemma mod_step {n u : ℕ} (hu : 2 ≤ u) (h : ¬u ∣ n+1) :
    (n+1)%u = n%u+1 := by
  have hone : 1%u = 1 := Nat.mod_eq_of_lt (by omega)
  have hne : (n+1)%u ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
  have hb : n % u < u := Nat.mod_lt _ (by omega)
  have hlt : n%u+1 < u := by
    by_contra! hn
    have he : n%u+1=u := by omega
    apply hne
    rw [Nat.add_mod, hone, he, Nat.mod_self]
  simpa only [hone] using Nat.add_mod_of_add_mod_lt (a:=n) (b:=1) (c:=u) (by simpa only [hone] using hlt)

private lemma residual_delta (c : ℕ →₀ ℚ) (r : ℕ) :
    residual c (r+1) - residual c r =
      residual c 1 - 1 + ∑ j ∈ c.support, if (j+2) ∣ (r+1) then c j else 0 := by
  classical
  let T (m j : ℕ) := c j * ((m % (j+2) : ℕ) : ℚ) / ((j+2 : ℕ) : ℚ)
  have hi (j : ℕ) : T 1 j + T r j - T (r+1) j =
      if (j+2) ∣ (r+1) then c j else 0 := by
    have he : 1 % (j+2) = 1 := Nat.mod_eq_of_lt (by omega)
    by_cases h : (j+2) ∣ (r+1)
    · have hm0 : (r+1) % (j+2) = 0 := Nat.mod_eq_zero_of_dvd h
      have hm1 : r % (j+2) + 1 = j+2 := by
        have hu := Nat.mod_lt r (show 0 < j+2 by omega)
        by_contra hne
        have hlt : r % (j+2)+1 < j+2 := by omega
        have hz := Nat.add_mod_of_add_mod_lt (a:=r) (b:=1) (c:=j+2) (by simpa [he] using hlt)
        rw [hm0, he] at hz
        omega
      simp only [T, he, hm0, if_pos h, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one,
        zero_div, sub_zero]
      have hmQ : (r % (j+2) : ℕ) + (1 : ℚ) = (j+2 : ℕ) := by exact_mod_cast hm1
      have hneq : ((j+2 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [← add_div, div_eq_iff hneq, ←hmQ]
      ring
    · have hm := mod_step (u:=j+2) (by omega) h
      simp only [T, he, hm, Nat.cast_add, Nat.cast_one, mul_one, if_neg h]
      ring
  have hsum := sum_congr (s₁:=c.support) rfl (fun j _ => hi j)
  simp only [sum_sub_distrib, sum_add_distrib] at hsum
  change (1-∑ j ∈ c.support, T (r+1) j) - (1-∑ j ∈ c.support, T r j) =
    (1-∑ j ∈ c.support, T 1 j) - 1 + _
  linarith

theorem all_coefficient_identity (c : ℕ →₀ ℚ) (n : ℕ) (hn : 2 ≤ n) :
    c (n-2) + (ArithmeticFunction.moebius n : ℚ) =
      (∑ d ∈ n.divisors.filter (1 < ·), (ArithmeticFunction.moebius (n/d):ℚ) * residual c d) -
      (∑ d ∈ n.divisors.filter (1 < ·), (ArithmeticFunction.moebius (n/d):ℚ) * residual c (d-1)) +
      (ArithmeticFunction.moebius n : ℚ) * residual c 1 := by
  classical
  let f (i : ℕ) : ℚ := (if 1 = i then residual c 1 - 1 else 0) +
    ∑ j ∈ c.support, if j+2 = i then c j else 0
  let g (d : ℕ) : ℚ := residual c d - residual c (d-1)
  have hg (m : ℕ) (hm : 0 < m) : ∑ i ∈ m.divisors, f i = g m := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp only [f, sum_add_distrib, g, Nat.succ_sub_one]
    rw [sum_comm (s:= (r+1).divisors) (t:=c.support)]
    simpa [Nat.mem_divisors, Nat.succ_ne_zero] using (residual_delta c r).symm
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f:=f) (g:=g)).mp hg n (by omega)
  rw [Nat.sum_divisorsAntidiagonal' (f:=fun x y => (ArithmeticFunction.moebius x : ℚ) * g y)] at hinv
  have hf : f n = c (n-2) := by
    have he (j : ℕ) : j+2 = n ↔ j=n-2 := by omega
    simp only [f, if_neg (by omega : ¬1=n), zero_add, he]
    by_cases h : n-2 ∈ c.support
    · simp [h]
    · simp [h, Finsupp.notMem_support_iff.mp h]
  rw [hf] at hinv
  let S := n.divisors.filter (1 < ·)
  have hsplit : n.divisors = insert 1 S := by
    ext d
    simp only [S, mem_insert, mem_filter]
    constructor
    · intro hd
      have hh := Nat.pos_of_mem_divisors hd
      by_cases h : d=1
      · exact Or.inl h
      · exact Or.inr ⟨hd,by omega⟩
    · rintro (rfl|⟨h,_⟩)
      · exact Nat.one_mem_divisors.mpr (by omega)
      · exact h
  have hnot : 1 ∉ S := by simp [S]
  rw [hsplit, sum_insert hnot] at hinv
  have hzero : residual c 0 = 1 := by simp [NymanBeurling.RationalGram.residual]
  simp only [g, Nat.div_one, Nat.sub_self, hzero, mul_sub, sum_sub_distrib] at hinv
  change _ = (∑ d ∈ S, _) - (∑ d ∈ S, _) + _
  linarith


end RationalGramProof

open Finset NymanBeurling.RationalGram
set_option maxHeartbeats 600000
namespace RationalGramProof
private def harmonic (c : ℕ →₀ ℚ) (N : ℕ) : ℚ :=
  ∑ d∈Ioc 0 N, |residual c d|/(d:ℚ)

private theorem coeff_abs (c : ℕ →₀ ℚ) {n : ℕ} (hn : 2 ≤ n) :
    |c (n-2)| ≤ 1+|residual c 1|+
      ∑ d∈n.divisors.filter (1<·), (|residual c d|+|residual c (d-1)|) := by
  let S := n.divisors.filter (1<·)
  let w := fun d => (ArithmeticFunction.moebius (n/d):ℚ)
  have hμ (j : ℕ) : |(ArithmeticFunction.moebius j:ℚ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=j)
  have hh (f : ℕ → ℚ) : |∑ d∈S,w d*f d| ≤ ∑ d∈S,|f d| := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum;intro d hd;rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hμ _)
  let U := ∑ d∈S,w d*residual c d
  let V := ∑ d∈S,w d*residual c (d-1)
  let a : ℚ := ArithmeticFunction.moebius n
  let r := residual c 1
  have he : c (n-2)=U-V+a*r-a := by
    apply eq_sub_of_add_eq
    exact all_coefficient_identity c n hn
  have hU : |U|≤∑ d∈S,|residual c d| := hh _
  have hV : |V|≤∑ d∈S,|residual c (d-1)| := hh (fun d => residual c (d-1))
  have hA : |a|≤1 := hμ n
  have hR : |a*r|≤|r| := by rw [abs_mul];exact mul_le_of_le_one_left (abs_nonneg r) hA
  rw [he,sum_add_distrib]
  calc
    _ ≤ |U-V+a*r|+|a| := abs_sub _ _
    _ ≤ (|U-V|+|a*r|)+|a| := add_le_add_left (abs_add_le _ _) _
    _ ≤ (|U|+|V|+|a*r|)+|a| := add_le_add_left (add_le_add_left (abs_sub _ _) _) _
    _ ≤ _ := by
      change _≤1+|r|+((∑ d∈S,|residual c d|)+∑ d∈S,|residual c (d-1)|)
      linarith only [hU,hV,hA,hR]

private theorem divisor_sum_fold (N : ℕ) (f : ℕ → ℚ) :
    ∑ n∈Ioc 1 N, ∑ d∈n.divisors.filter (1<·), f d =
      ∑ d∈Ioc 1 N, ((N/d:ℕ):ℚ)*f d := by
  classical
  let S := Ioc 1 N
  have he (n : ℕ) (hn : n∈S) : n.divisors.filter (1<·)=S.filter (·∣n) := by
    ext d
    obtain ⟨hn1,hn2⟩ := mem_Ioc.mp hn
    simp only [S,mem_filter,Nat.mem_divisors,mem_Ioc]
    constructor
    · rintro ⟨⟨hd,_⟩,h1⟩;exact ⟨⟨h1,(Nat.le_of_dvd (by omega) hd).trans hn2⟩,hd⟩
    · rintro ⟨⟨h1,_⟩,hd⟩;exact ⟨⟨hd,by omega⟩,h1⟩
  change (∑ n∈S,_) = ∑ d∈S,_
  calc
    _ = ∑ n∈S,∑ d∈S,if d∣n then f d else 0 := by
      apply sum_congr rfl;intro n hn;rw [he n hn,sum_filter]
    _ = _ := by
      rw [sum_comm];apply sum_congr rfl;intro d hd
      rw [←sum_filter,sum_const,nsmul_eq_mul]
      have heq : S.filter (d∣·) = (Ioc 0 N).filter (d∣·) := by
        ext t;simp only [S,mem_filter,mem_Ioc]
        have hd1 := (mem_Ioc.mp hd).1
        constructor
        · rintro ⟨⟨h1,h2⟩,h3⟩;exact ⟨⟨by omega,h2⟩,h3⟩
        · rintro ⟨⟨h1,h2⟩,h3⟩;exact ⟨⟨lt_of_lt_of_le hd1 (Nat.le_of_dvd h1 h3),h2⟩,h3⟩
      rw [heq,Nat.Ioc_filter_dvd_card_eq_div]

private theorem previous_harmonic (c : ℕ →₀ ℚ) (N : ℕ) :
    ∑ d∈Ioc 1 N, |residual c (d-1)|/(d:ℚ) ≤ harmonic c N := by
  let S := Ioc 1 N
  have hinj : Set.InjOn (fun d : ℕ => d-1) (S:Set ℕ) := by
    intro a ha b hb he;change a-1=b-1 at he;have : 1 < a := (mem_Ioc.mp ha).1;have : 1 < b := (mem_Ioc.mp hb).1;omega
  let T := S.image (fun d => d-1)
  have hsub : T⊆Ioc 0 N := by
    intro j hj;obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
    obtain ⟨h1,h2⟩ := mem_Ioc.mp hd;apply mem_Ioc.mpr;omega
  calc
    _ ≤ ∑ d∈S,|residual c (d-1)|/((d-1:ℕ):ℚ) := by
      apply sum_le_sum;intro d hd
      have hh := (mem_Ioc.mp hd).1
      apply div_le_div_of_nonneg_left (abs_nonneg _) (by exact_mod_cast (show 0 < d-1 by omega))
      exact_mod_cast Nat.sub_le d 1
    _ = ∑ j∈T,|residual c j|/(j:ℚ) := (sum_image (f:=fun j : ℕ => |residual c j|/(j:ℚ)) (g:=fun j : ℕ => j-1) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

private theorem current_harmonic (c : ℕ →₀ ℚ) (N : ℕ) :
    ∑ d∈Ioc 1 N,|residual c d|/(d:ℚ) ≤ harmonic c N :=
  sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc (by decide) le_rfl) (fun _ _ _ => by positivity)

private theorem support_sum_le (c : ℕ →₀ ℚ) {N : ℕ} (hs : ∀ k∈c.support,k+2 ≤ N) :
    (∑ i∈c.support,|c i|) ≤ ∑ n∈Ioc 1 N, |c (n-2)| := by
  let T := c.support.image (fun i => i+2)
  have hsub : T ⊆ Ioc 1 N := by
    intro n h;obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact mem_Ioc.mpr ⟨by omega,hs i hi⟩
  calc
    _ = ∑ n∈T,|c (n-2)| := by
      rw [show T=c.support.image (fun i => i+2) from rfl,sum_image]
      · simp
      · intro i hi j hj;dsimp;omega
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

private theorem mass_linear (c : ℕ →₀ ℚ) {N : ℕ} (hN : 1 ≤ N) (hs : ∀ k∈c.support,k+2 ≤ N) :
    mass c ≤ 1+N+3*(N:ℚ)*harmonic c N := by
  let S := Ioc 1 N
  let A := 1+|residual c 1|
  let V := fun d : ℕ => |residual c d|+|residual c (d-1)|
  have hb : (∑ i∈c.support,|c i|) ≤ ∑ n∈S,(A+∑ d∈n.divisors.filter (1<·),V d) :=
    (support_sum_le c hs).trans (sum_le_sum fun n hn => coeff_abs c (mem_Ioc.mp hn).1)
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,divisor_sum_fold N V] at hb
  have hcard : (S.card:ℚ) ≤ N := by
    change ((Ioc 1 N).card:ℚ) ≤ N
    simp only [Nat.card_Ioc];exact_mod_cast Nat.sub_le N 1
  have hv : (∑ d∈S, ((N/d:ℕ):ℚ)*V d) ≤ (N:ℚ)*(2*harmonic c N) := by
    calc
      _ ≤ ∑ d∈S,(N:ℚ)*(V d/d) := by
        apply sum_le_sum;intro d hd
        exact (mul_le_mul_of_nonneg_right Nat.cast_div_le (by dsimp [V];positivity)).trans_eq (by ring)
      _ = (N:ℚ)*((∑ d∈S,|residual c d|/(d:ℚ)) + ∑ d∈S,|residual c (d-1)|/(d:ℚ)) := by
        simp only [V,←mul_sum,add_div,sum_add_distrib]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [current_harmonic c N,previous_harmonic c N]
  have h1 : |residual c 1| ≤ harmonic c N := by
    have := single_le_sum (f:=fun d : ℕ => |residual c d|/(d:ℚ))
      (s:=Ioc 0 N) (fun d _ => by positivity) (mem_Ioc.mpr ⟨(by decide : (0:ℕ)<1),hN⟩)
    simpa only [Nat.cast_one,div_one,harmonic] using this
  have hcard' := mul_le_mul_of_nonneg_right hcard (by dsimp [A];positivity : 0 ≤ A)
  have hN1 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N : (0:ℚ) ≤ N)
  dsimp only [mass,A] at *
  linarith only [hb,hv,hcard',hN1]

private theorem sum_pos_to_range {M : Type*} [AddCommMonoid M] (f : ℕ→M) (N : ℕ) :
    ∑ d∈Ioc 0 N,f d=∑ i∈range N,f (i+1) := by
  induction N with
  | zero => simp
  | succ n h =>
    rw [←insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le n),sum_insert (by simp),sum_range_succ,h,add_comm]

private theorem harmonic_sq (c : ℕ →₀ ℚ) (N : ℕ) :
    (harmonic c N)^2 ≤ 2*(N:ℚ)*headEnergy c N := by
  rw [harmonic,sum_pos_to_range]
  have hcs := sum_mul_sq_le_sq_mul_sq (range N) (fun _ => (1:ℚ))
    (fun i => |residual c (i+1)| / ((i+1:ℕ):ℚ))
  simp only [one_mul,one_pow,sum_const,card_range,nsmul_eq_mul,mul_one] at hcs
  apply hcs.trans
  rw [mul_comm (2:ℚ) (N:ℚ),mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  rw [headEnergy,mul_sum]
  apply sum_le_sum;intro i hi
  rw [div_pow,sq_abs,Nat.cast_add,Nat.cast_one]
  have hA : (0:ℚ) < i+1 := by positivity
  have hB : (0:ℚ) < i+2 := by positivity
  field_simp
  nlinarith [mul_nonneg (sq_nonneg (residual c (i+1))) (Nat.cast_nonneg i : (0:ℚ) ≤ i)]

theorem mass_sq_le_head (c : ℕ →₀ ℚ) {N : ℕ} (hN : 1 ≤ N) (hs : ∀ k∈c.support,k+2 ≤ N) :
    (mass c)^2 ≤ 2*(N+1:ℚ)^2+36*(N:ℚ)^3*headEnergy c N := by
  have hm := mass_linear c hN hs
  have hM : 0 ≤ mass c := by unfold mass;positivity
  have hS : 0 ≤ harmonic c N := by unfold harmonic;positivity
  have h1 := (sq_le_sq₀ hM (by positivity)).mpr hm
  have h2 := harmonic_sq c N
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0:ℚ)≤18*(N:ℚ)^2 by positivity)
  nlinarith only [h1,h3,sq_nonneg (1+(N:ℚ)-3*N*harmonic c N)]
end RationalGramProof
open Finset Matrix Set NymanBeurling.RationalGram
open scoped Matrix 
namespace RationalGramProof
noncomputable section

def vector {D : ℕ} (x : Fin D→ℚ) : ℕ →₀ ℚ :=
  Finsupp.embDomain Fin.valEmbedding (Finsupp.equivFunOnFinite.symm x)

theorem vector_apply {D : ℕ} (x : Fin D→ℚ) (i : Fin D) : vector x i=x i := by
  change (Finsupp.embDomain Fin.valEmbedding _) (Fin.valEmbedding i)=_
  rw [Finsupp.embDomain_apply_self];rfl
theorem vector_bound {D : ℕ} (x : Fin D→ℚ) (j : ℕ) (hj : j∈(vector x).support) : j+2≤D+1 := by
  rw [vector,Finsupp.support_embDomain] at hj
  obtain ⟨i,hi,rfl⟩ := mem_map.mp hj
  change i.val+2≤D+1;have := i.isLt;omega

theorem vector_sum {D : ℕ} (x : Fin D→ℚ) (f : ℕ→ℚ→ℚ) (hf : ∀ i,f i 0=0) :
    ∑ j∈(vector x).support,f j (vector x j) = ∑ i : Fin D,f i (x i) := by
  change Finsupp.sum (vector x) f = _
  rw [vector,Finsupp.sum_embDomain,Finsupp.sum_fintype _ _ (fun i=>hf _)]
  rfl

theorem design_row {D H : ℕ} (x : Fin D→ℚ) (n : Fin H) :
    residual (vector x) (n.val+1)=1-(design D H *ᵥ x) n := by
  rw [NymanBeurling.RationalGram.residual,vector_sum x (fun i q => q*((n.val+1)%(i+2):ℕ)/((i+2:ℕ):ℚ)) (by simp)]
  congr 1;apply sum_congr rfl;intro i _
  change _=atom i n*x i
  simp only [atom,Nat.cast_add,Nat.cast_ofNat];ring

private theorem design_kernel {D H : ℕ} (hH : D+1≤H) {x : Fin D→ℚ} (hx : design D H *ᵥ x=0) : x=0 := by
  have hhead (m : ℕ) (hm : 0 < m) (hm' : m≤H) : residual (vector x) m=1 := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hh := design_row x (⟨i,by omega⟩ : Fin H)
    simpa only [hx,Pi.zero_apply,sub_zero] using hh
  funext i
  let d := i.val+2
  have hd : 2≤d := by dsimp [d];omega
  have hdH : d≤H := by dsimp [d];have := i.isLt;omega
  have he := all_coefficient_identity (vector x) d hd
  let S := d.divisors.filter (1<·)
  have h1 (j : ℕ) (hj : j∈S) : 1<j ∧ j≤H := ⟨(mem_filter.mp hj).2,(Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors (mem_filter.mp hj).1)).trans hdH⟩
  have hs : (∑ j∈S,(ArithmeticFunction.moebius (d/j):ℚ)*residual (vector x) j)=
      ∑ j∈S,(ArithmeticFunction.moebius (d/j):ℚ)*residual (vector x) (j-1) := by
    apply sum_congr rfl;intro j hj;obtain ⟨h,h'⟩:=h1 j hj
    rw [hhead _ (by omega) h',hhead _ (by omega) (by omega)]
  rw [hs,hhead 1 (by decide) (by omega),sub_self,zero_add,mul_one] at he
  have hx0 := add_right_cancel (b:= (ArithmeticFunction.moebius d : ℚ)) (c:=0) (by simpa using he)
  change x i=0
  simpa only [d,Nat.add_sub_cancel,vector_apply] using hx0

def energy {D H : ℕ} (x : Fin D→ℚ) := ∑ n : Fin H, weight n*(1-(design D H *ᵥ x) n)^2
def quadratic {D H : ℕ} (x : Fin D→ℚ) := ∑ n : Fin H, weight n*((design D H *ᵥ x) n)^2
theorem prefix_vec {D H : ℕ} (x : Fin D→ℚ) : headEnergy (vector x) H=energy (H:=H) x := by
  rw [headEnergy,←Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl;intro i hi
  rw [design_row];unfold weight;ring

theorem gram_action {D H : ℕ} (x y : Fin D→ℚ) :
    x ⬝ᵥ (gram D H *ᵥ y) = ∑ i : Fin H,weight i*(design D H *ᵥ x) i*(design D H *ᵥ y) i := by
  rw [NymanBeurling.RationalGram.gram,←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
  apply sum_congr rfl;intro n _;rw [mulVec_diagonal];ring

theorem target_action {D H : ℕ} (x : Fin D→ℚ) :
    x ⬝ᵥ target D H = ∑ i : Fin H,weight i*(design D H *ᵥ x) i := by
  rw [target,dotProduct_mulVec,vecMul_transpose]
  apply sum_congr rfl;intro n _;ring

theorem gram_unit {D H : ℕ} (hH : D+1≤H) : IsUnit (gram D H) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  apply (injective_iff_map_eq_zero (gram D H).mulVecLin).mpr
  intro x hx
  change gram D H *ᵥ x=0 at hx
  apply design_kernel hH
  have he := gram_action (H:=H) x x
  rw [hx,dotProduct_zero] at he
  have hp (n : Fin H) : 0<weight n := by unfold weight;positivity
  have h0 := (sum_eq_zero_iff_of_nonneg (fun (n : Fin H) _ => (show 0≤weight n*(design D H *ᵥ x) n*(design D H *ᵥ x) n by
    rw [mul_assoc,←sq];exact mul_nonneg (hp n).le (sq_nonneg _)))).mp he.symm
  funext i
  have h := h0 i (mem_univ _)
  change (design D H *ᵥ x) i=0
  rw [mul_assoc,←sq] at h
  exact pow_eq_zero_iff (by decide : 2≠0) |>.mp ((mul_eq_zero.mp h).resolve_left (hp i).ne')

end
end RationalGramProof

open Matrix Finset NymanBeurling.RationalGram
open scoped Matrix
namespace RationalGramProof
noncomputable section

def optimal (D H : ℕ) : Fin D → ℚ := (gram D H)⁻¹ *ᵥ target D H

private theorem normal {D H : ℕ} (hr : D+1≤H) :
    gram D H *ᵥ optimal D H=target D H := by
  rw [optimal,mulVec_mulVec,mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (gram_unit hr)),one_mulVec]

private theorem orthogonal {D H : ℕ} (hr : D+1≤H) (x : Fin D→ℚ) :
    ∑ i : Fin H,weight i*(design D H *ᵥ x) i*(1-(design D H *ᵥ optimal D H) i)=0 := by
  have he := gram_action (H:=H) x (optimal D H)
  rw [normal hr,target_action] at he
  simp only [mul_sub,mul_one,sum_sub_distrib,←he,sub_self]

private theorem optimal_formula {D H : ℕ} (hr : D+1≤H) :
    energy (H:=H) (optimal D H) = (∑ i : Fin H,weight i) - target D H ⬝ᵥ optimal D H := by
  let z := optimal D H
  let u := design D H *ᵥ z
  have hv := orthogonal hr z
  change (∑ i : Fin H,weight i*u i*(1-u i))=0 at hv
  rw [dotProduct_comm,target_action]
  change (∑ i : Fin H,weight i*(1-u i)^2)= (∑ i : Fin H,weight i)-∑ i : Fin H,weight i*u i
  calc
    _ = ∑ i : Fin H, ((weight i-weight i*u i)-weight i*u i*(1-u i)) := by apply sum_congr rfl;intro i hi;ring
    _ = _ := by rw [sum_sub_distrib,sum_sub_distrib,hv,sub_zero]

theorem gap_eq {D H : ℕ} (hr : D+1≤H) :
    gap D H = energy (H:=H) (optimal D H) := by
  classical
  let G := NymanBeurling.RationalGram.gram D H
  let b := target D H
  let u : Matrix (Fin D) Unit ℚ := Matrix.of fun i _ => b i
  let v : Matrix Unit (Fin D) ℚ := Matrix.of fun _ i => b i
  let S : Matrix Unit Unit ℚ := Matrix.of fun _ _ => ∑ i : Fin H,weight i
  let _ := (gram_unit hr).nonempty_invertible.some
  have he : (v * G⁻¹ * u) () () = b ⬝ᵥ optimal D H := by rw [Matrix.mul_assoc];rfl
  rw [optimal_formula hr]
  change (Matrix.fromBlocks G u v S).det/G.det=_
  rw [det_fromBlocks₁₁,Matrix.det_unique (S - v * ⅟G * u),Matrix.sub_apply,invOf_eq_nonsing_inv,he]
  change G.det*((∑ i : Fin H,weight i)-b ⬝ᵥ optimal D H)/G.det=_
  exact mul_div_cancel_left₀ _ ((isUnit_iff_isUnit_det _).mp (gram_unit hr)).ne_zero

theorem gap_le {D H : ℕ} (hr : D+1≤H) (x : Fin D→ℚ) : gap D H ≤ energy (H:=H) x := by
  let z := optimal D H
  let v := x-z
  let u := design D H *ᵥ z
  let t := design D H *ᵥ v
  have he (i : Fin H) : (design D H *ᵥ x) i=u i+t i := by
    have hi : x=z+v := by dsimp [v];abel
    rw [hi,mulVec_add];rfl
  have ho := orthogonal hr v
  change (∑ i : Fin H, weight i*t i*(1-u i))=0 at ho
  rw [gap_eq hr]
  change (∑ i : Fin H,weight i*(1-u i)^2)≤∑ i : Fin H,weight i*(1-(design D H *ᵥ x) i)^2
  simp_rw [he]
  have hx : (∑ i : Fin H,weight i*(1-(u i+t i))^2)=
      (∑ i : Fin H,weight i*(1-u i)^2)+(∑ i : Fin H,weight i*(t i)^2)-2*∑ i : Fin H,weight i*t i*(1-u i) := by
    rw [mul_sum,←sum_add_distrib,←sum_sub_distrib];apply sum_congr rfl;intro i hi;ring
  rw [hx,ho,mul_zero,sub_zero];apply le_add_of_nonneg_right
  apply sum_nonneg;intro i hi;unfold weight;positivity

theorem gap_nonneg {D H : ℕ} (hr : D+1≤H) : 0 ≤ gap D H := by
  rw [gap_eq hr,energy];apply sum_nonneg;intro i hi;unfold weight;positivity
end
end RationalGramProof

open Matrix Finset Filter Topology NymanBeurling.RationalGram
namespace RationalGramProof
noncomputable section

theorem residual_le (c : ℕ →₀ ℚ) (m : ℕ) : |residual c m| ≤ mass c := by
  rw [NymanBeurling.RationalGram.residual,mass]
  apply (abs_sub _ _).trans
  rw [abs_one]
  gcongr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum;intro i hi
  have hd : (0:ℚ)<((i+2:ℕ):ℚ) := by positivity
  have hmod : ((m%(i+2):ℕ):ℚ) ≤ ((i+2:ℕ):ℚ) := by exact_mod_cast (Nat.mod_lt m (by omega : 0 < i+2)).le
  rw [abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg (m%(i+2)) : (0:ℚ) ≤ ↑(m%(i+2))),abs_of_pos hd,div_le_iff₀ hd]
  exact mul_le_mul_of_nonneg_left hmod (abs_nonneg _)

theorem head_mono (c : ℕ →₀ ℚ) : Monotone (headEnergy c) := by
  apply monotone_nat_of_le_succ;intro n
  simp only [headEnergy,sum_range_succ];apply le_add_of_nonneg_right;positivity

theorem cost_anti (c : ℕ →₀ ℚ) : Antitone (cost c) := by
  apply antitone_nat_of_succ_le;intro n
  have ha := residual_le c (n+1)
  have hs := (sq_le_sq₀ (abs_nonneg _) (by unfold mass;positivity)).mpr ha
  rw [sq_abs] at hs
  simp only [cost,headEnergy,sum_range_succ,Nat.cast_succ]
  have h1 : (0:ℚ)<n+1 := by positivity
  have h2 : (0:ℚ)<n+2 := by positivity
  rw [show (n:ℚ)+1+1=n+2 by ring]
  field_simp
  nlinarith only [hs]

theorem head_le_cost (c : ℕ →₀ ℚ) (H K : ℕ) : headEnergy c H ≤ cost c K := by
  have h (n : ℕ) : headEnergy c n ≤ cost c n := by unfold cost;apply le_add_of_nonneg_right;positivity
  rcases le_total H K with h'|h'
  · exact (head_mono c h').trans (h K)
  · exact (h H).trans (cost_anti c h')

theorem gap_one {D H : ℕ} (hH : D+1≤H) : gap D H ≤ 1 := by
  have he : vector (0 : Fin D→ℚ)=0 := by unfold vector;rw [show Finsupp.equivFunOnFinite.symm (0 : Fin D→ℚ)=0 from by ext i;rfl];simp
  have hb := gap_le hH (0 : Fin D→ℚ)
  rw [←prefix_vec,he] at hb
  exact hb.trans ((head_le_cost 0 H 0).trans_eq (by simp [cost,headEnergy,mass]))

theorem row_count (D : ℕ) : D+1 ≤ rows D := by
  unfold rows
  calc
    D+1 ≤ D+2 := by omega
    _ ≤ (D+2)^4 := Nat.le_self_pow (by decide) _

theorem finite_budget (D : ℕ) :
    ∃ c : ℕ →₀ ℚ, (∀ k ∈ c.support,k < D) ∧
    headEnergy c (rows D)=gap D (rows D) ∧ cost c (rows D) ≤ gap D (rows D)+38/(D+2:ℚ) := by
  let c := vector (optimal D (rows D))
  have hrc := row_count D
  have hf := vector_bound (optimal D (rows D))
  have he : headEnergy c (rows D) = gap D (rows D) := (prefix_vec _).trans (gap_eq hrc).symm
  refine ⟨c,fun i hi => by have := hf i hi;omega,he,?_⟩
  have hm := mass_sq_le_head c (N:=D+1) (by omega) hf
  have h₁ := (head_mono c hrc).trans (he.le.trans (gap_one hrc))
  simp only [Nat.cast_add,Nat.cast_one] at hm
  have h₂ := mul_le_mul_of_nonneg_left h₁ (by positivity : (0:ℚ) ≤ 36*(D+1:ℚ)^3)
  have hm' : (mass c)^2 ≤ 38*(D+2:ℚ)^3 := by nlinarith [sq_nonneg (D:ℚ),pow_nonneg (Nat.cast_nonneg D : (0:ℚ) ≤ D) 3]
  rw [cost,he]
  apply add_le_add_right
  simp only [rows,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
  calc
    _ ≤ (38*(D+2:ℚ)^3)/((D+2:ℚ)^4+1) := by gcongr
    _ ≤ (38*(D+2:ℚ)^3)/(D+2:ℚ)^4 := by apply div_le_div_of_nonneg_left (by positivity) (by positivity);linarith
    _ = _ := by field_simp

theorem lower_bound {D H : ℕ} (hr : D+1≤H) (c : ℕ →₀ ℚ) (hs : ∀ k ∈ c.support,k < D) (K : ℕ) :
    gap D H ≤ cost c K := by
  let x : Fin D→ℚ := fun i=>c i
  have he : vector x=c := by
    ext k
    by_cases h : k < D
    · exact vector_apply x ⟨k,h⟩
    · have hc : k ∉ c.support := fun hk => h (hs k hk)
      have hv : k ∉ (vector x).support := by intro hk;have := vector_bound x k hk;omega
      rw [Finsupp.notMem_support_iff.mp hc,Finsupp.notMem_support_iff.mp hv]
  have hb := gap_le hr x
  rw [←prefix_vec,he] at hb
  exact hb.trans (head_le_cost c H K)

theorem criterion : SmallCertificates ↔ Tendsto (fun D => gap D (rows D)) atTop (𝓝 0) := by
  constructor
  · intro hc
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨J,hJ⟩ := (Metric.tendsto_atTop.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ))) ε hε
    obtain ⟨c,K,hK⟩ := hc J
    refine ⟨c.support.sup id+1,?_⟩
    intro D hD
    have hs (k : ℕ) (hk : k ∈ c.support) : k<D := by
      have hh : k ≤ c.support.sup id := Finset.le_sup (f:=id) hk
      omega
    have hg := lower_bound (row_count D) c hs K
    have ht := hJ J le_rfl
    simp only [Rat.dist_eq,Rat.cast_zero,sub_zero] at ht ⊢
    have hn : (0:ℚ) ≤ 1/(J+1:ℚ) := by positivity
    rw [abs_of_nonneg (by exact_mod_cast hn : (0:ℝ) ≤ ((1/(J+1:ℚ):ℚ):ℝ))] at ht
    rw [abs_of_nonneg (by exact_mod_cast gap_nonneg (row_count D) : (0:ℝ) ≤ (gap D (rows D):ℝ))]
    have hb : (gap D (rows D):ℝ) < ((1/(J+1:ℚ):ℚ):ℝ) := by exact_mod_cast hg.trans_lt hK
    exact hb.trans ht
  · intro hg J
    let t : ℚ := 1/(J+1:ℚ)
    have ht : 0 < t := by dsimp [t];positivity
    have hv : Tendsto (fun D : ℕ => (38:ℚ)/(D+1:ℚ)) atTop (𝓝 0) := by
      simpa only [mul_zero,mul_one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).const_mul 38
    have h1 := hg.eventually_lt_const (by linarith : (0:ℚ)<t/2)
    have h2 := hv.eventually_lt_const (by linarith : (0:ℚ)<t/2)
    obtain ⟨D,hg',hv'⟩ := (h1.and h2).exists
    obtain ⟨c,hs,he,hc⟩ := finite_budget D
    refine ⟨c,rows D,hc.trans_lt ?_⟩
    change gap D (rows D)<t/2 at hg'
    change (38:ℚ)/(D+1:ℚ)<t/2 at hv'
    have hv₂ : (38:ℚ)/(D+2:ℚ) ≤ 38/(D+1:ℚ) := by gcongr;linarith
    change gap D (rows D)+38/(D+2:ℚ)<t
    linarith
end
end RationalGramProof
set_option maxHeartbeats 2500000
open Matrix Finset Filter Topology NymanBeurling.RationalGram
namespace RationalGramProof
noncomputable section

theorem bound_for_rows {D H : ℕ} (hr : D+1 ≤ H) :
    ∃ c : ℕ →₀ ℚ, (∀ k ∈ c.support,k < D) ∧ headEnergy c H=gap D H ∧
      cost c H ≤ gap D H+(2*(D+2:ℚ)^2+36*(D+1:ℚ)^3*gap D H)/(H+1:ℚ) := by
  let c := vector (optimal D H)
  have hf := vector_bound (optimal D H)
  have he : headEnergy c H=gap D H := (prefix_vec _).trans (gap_eq hr).symm
  refine ⟨c,fun k hk => by have := hf k hk;omega,he,?_⟩
  have h1 := (head_mono c hr).trans he.le
  have hm := mass_sq_le_head c (N:=D+1) (by omega) hf
  rw [cost,he]
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp only [Nat.cast_add,Nat.cast_one] at hm
  rw [show (D:ℚ)+1+1=D+2 by ring] at hm
  exact hm.trans (add_le_add_right (mul_le_mul_of_nonneg_left h1 (show (0:ℚ) ≤ 36*(D+1:ℚ)^3 by positivity)) _)

theorem cubic_budget {D H : ℕ} (hc : (D+2)^3 ≤ H) :
    ∃ c : ℕ →₀ ℚ, cost c H ≤ 37*gap D H+2/(D+2:ℚ) := by
  have hr : D+1≤H := calc
    D+1 ≤ D+2 := by omega
    _ ≤ (D+2)^3 := Nat.le_self_pow (by decide) _
    _ ≤ H := hc
  obtain ⟨c,hs,he,hc'⟩ := bound_for_rows hr
  refine ⟨c,hc'.trans ?_⟩
  have hn := gap_nonneg hr
  have hh : (D+2:ℚ)^3 ≤ (H:ℚ) := by exact_mod_cast hc
  have hb : (0:ℚ)<D+2 := by positivity
  calc
    _ ≤ gap D H+(2*(D+2:ℚ)^2+36*(D+2:ℚ)^3*gap D H)/(D+2:ℚ)^3 := by
      apply add_le_add_right
      apply div_le_div₀ (by positivity) _ (by positivity) (by linarith)
      gcongr;linarith
    _ = _ := by field_simp;ring

theorem arbitrary_cubic_criterion (h : ℕ→ℕ) (hrow : ∀ D,(D+2)^3≤h D) :
    SmallCertificates ↔ Tendsto (fun D=>gap D (h D)) atTop (𝓝 0) := by
  have hr (D : ℕ) : D+1≤h D := calc
    D+1 ≤ D+2 := by omega
    _ ≤ (D+2)^3 := Nat.le_self_pow (by decide) _
    _ ≤ h D := hrow D
  constructor
  · intro hc
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n=>ha.trans_le (gap_nonneg (hr n)))
    · intro b hb
      have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).eventually_lt_const hb
      obtain ⟨J,hJ⟩ := ht.exists
      obtain ⟨c,K,hK⟩ := hc J
      apply eventually_atTop.mpr
      refine ⟨c.support.sup id+1,?_⟩;intro D hD
      have hs (k : ℕ) (hk : k∈c.support) : k < D := by
        have hh : k≤c.support.sup id := Finset.le_sup (f:=id) hk
        omega
      exact (lower_bound (hr D) c hs K).trans_lt (hK.trans hJ)
  · intro hg J
    let t : ℚ := 1/(J+1:ℚ)
    have ht : 0 < t := by dsimp [t];positivity
    have hg' : Tendsto (fun D=>37*gap D (h D)) atTop (𝓝 (0:ℚ)) := by simpa using hg.const_mul 37
    have hv : Tendsto (fun D : ℕ => (2:ℚ)/(D+1:ℚ)) atTop (𝓝 0) := by
      simpa only [mul_zero,mul_one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).const_mul 2
    have hsum : Tendsto (fun D=>37*gap D (h D)+2/(D+1:ℚ)) atTop (𝓝 (0:ℚ)) := by simpa using hg'.add hv
    obtain ⟨D,hD⟩ := (hsum.eventually_lt_const ht).exists
    obtain ⟨c,hb⟩ := cubic_budget (hrow D)
    refine ⟨c,h D,hb.trans_lt ?_⟩
    apply lt_of_le_of_lt _ hD
    apply add_le_add_right
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity);linarith
end
end RationalGramProof
open NymanBeurling.RationalGram Filter Topology RationalGramProof

theorem solution :
    (∀ (c : ℕ →₀ ℚ) (N : ℕ), 1 ≤ N → (∀ k ∈ c.support, k+2 ≤ N) →
      (mass c)^2 ≤ 2*(N+1:ℚ)^2+36*(N:ℚ)^3*headEnergy c N) ∧
    (∀ (D H : ℕ), D+1 ≤ H →
      (NymanBeurling.RationalGram.gram D H).det ≠ 0 ∧ 0 ≤ gap D H ∧
      (∀ (c : ℕ →₀ ℚ), (∀ k ∈ c.support, k < D) → ∀ K, gap D H ≤ cost c K) ∧
      ∃ c : ℕ →₀ ℚ, (∀ k ∈ c.support, k < D) ∧ headEnergy c H = gap D H ∧
        cost c H ≤ gap D H+(2*(D+2:ℚ)^2+36*(D+1:ℚ)^3*gap D H)/(H+1:ℚ)) ∧
    (∀ D, ∃ c : ℕ →₀ ℚ, (∀ k ∈ c.support, k < D) ∧
      headEnergy c (rows D) = gap D (rows D) ∧
      cost c (rows D) ≤ gap D (rows D)+38/(D+2:ℚ)) ∧
    (SmallCertificates ↔ Tendsto (fun D => gap D (rows D)) atTop (𝓝 0)) ∧
    (∀ h : ℕ → ℕ, (∀ D, (D+2)^3 ≤ h D) →
      (SmallCertificates ↔ Tendsto (fun D => gap D (h D)) atTop (𝓝 0))) := by
  refine ⟨fun c _ hn hs => mass_sq_le_head c hn hs,?_,finite_budget,criterion,arbitrary_cubic_criterion⟩
  intro D H h
  exact ⟨((Matrix.isUnit_iff_isUnit_det _).mp (gram_unit h)).ne_zero,gap_nonneg h,
    fun c hs K => lower_bound h c hs K,bound_for_rows h⟩
