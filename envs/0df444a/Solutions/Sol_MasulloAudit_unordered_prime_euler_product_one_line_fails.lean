-- Prove2me | solution 1 for MasulloAudit.unordered_prime_euler_product_one_line_fails
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:33:37.610772+00:00
-- url     : https://prove2.me/submissions/b4a608e8-0fd3-4f4e-8dc5-a59338ebf852

import Theorems.Thm_MasulloRH_partialEulerProduct_tendsto_riemannZeta_one_line

open Complex Filter Topology Set
noncomputable section

private theorem prod_tail {ι : Type*} (f : ι→ℂ) (hf : ∀ i, f i≠0) {L : ℂ} (hL : L≠0)
    (hp : HasProd f L) (η : ℝ) (hη : 0<η) :
    ∃ S : Finset ι, ∀ T : Finset ι, Disjoint T S → ‖(∏ i ∈ T,f i)-1‖<η := by
  classical
  let P (s : Finset ι) := ∏ i ∈ s, f i
  have hh : Tendsto P atTop (𝓝 L) := hp
  have hd : Tendsto (fun u : Finset ι × Finset ι => P u.1/P u.2) atTop (𝓝 1) := by
    rw [←prod_atTop_atTop_eq]
    have h : Tendsto (fun u : Finset ι × Finset ι => P u.1/P u.2) (atTop ×ˢ atTop) (𝓝 (L/L)) :=
      (hh.comp tendsto_fst).div (hh.comp tendsto_snd) hL
    simpa only [div_self hL] using h
  obtain ⟨v,hv⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hd η hη)
  let S := v.1 ∪ v.2
  refine ⟨S,fun T hT => ?_⟩
  have h := hv (T ∪ S,S) (show v≤(T ∪ S,S) from
    ⟨Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right,Finset.subset_union_right⟩)
  have hn : P S≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)
  simpa only [dist_eq_norm,P,Finset.prod_union hT,mul_div_cancel_right₀ _ hn] using h

private theorem pos_real {z : ℂ} (h : ‖z-1‖<1) : 0<z.re := by
  have hh := Complex.re_le_norm (1-z)
  rw [norm_sub_rev,Complex.sub_re,Complex.one_re] at hh
  linarith

private theorem log_mul_pos {x y : ℂ} (hx : 0<x.re) (hy : 0<y.re) :
    Complex.log (x*y)=Complex.log x+Complex.log y := by
  have hnx : x≠0 := fun h => by simpa [h] using hx
  have hny : y≠0 := fun h => by simpa [h] using hy
  apply (Complex.log_mul_eq_add_log_iff hnx hny).mpr
  obtain ⟨hx1,hx2⟩ := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (.inl hx))
  obtain ⟨hy1,hy2⟩ := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (.inl hy))
  constructor <;> linarith

private theorem sum_log_of_nonzero_prod {ι : Type*} (f : ι→ℂ) (hf : ∀ i,f i≠0) {L : ℂ} (hL : L≠0)
    (hp : HasProd f L) : Summable (fun i => Complex.log (f i)) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  let η := min (1/2:ℝ) (ε/2)
  obtain ⟨S,hS⟩ := prod_tail f hf hL hp η (lt_min (by norm_num) (by positivity))
  have hhalf : η ≤ 1/2 := min_le_left _ _
  have hpos (t : Finset ι) (ht : Disjoint t S) : 0<(∏ i ∈ t,f i).re :=
    pos_real ((hS t ht).trans_le (by linarith))
  have hid (t : Finset ι) (ht : Disjoint t S) : ∑ i ∈ t, Complex.log (f i)=Complex.log (∏ i ∈ t,f i) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      obtain ⟨his,hts⟩ := Finset.disjoint_insert_left.mp ht
      have hfi : 0<(f i).re := by simpa using hpos {i} (Finset.disjoint_singleton_left.mpr his)
      rw [Finset.sum_insert hi,Finset.prod_insert hi,log_mul_pos hfi (hpos t hts),ih hts]
  refine ⟨S,fun t ht => ?_⟩
  rw [hid t ht]
  let z := ∏ i ∈ t,f i
  have hh : ‖z-1‖<η := hS t ht
  have hb := Complex.norm_log_one_add_half_le_self (hh.le.trans hhalf)
  rw [show (1:ℂ)+(z-1)=z by ring] at hb
  have hη : η≤ε/2 := min_le_right _ _
  change ‖Complex.log z‖<ε
  linarith

private theorem nonzero_impossible (s : ℂ) (hs : s.re=1) {L : ℂ} (hL : L≠0) :
    ¬HasProd (fun p : Nat.Primes => (1-(p:ℂ)^(-s))⁻¹) L := by
  let z (p : Nat.Primes) := (p:ℂ)^(-s)
  let f (p : Nat.Primes) := (1-z p)⁻¹
  have hn (p : Nat.Primes) : ‖z p‖=(1/(p:ℝ)) := by
    change ‖((p.val:ℕ):ℂ)^(-s)‖=1/((p.val:ℕ):ℝ)
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re,hs,Real.rpow_neg_one,one_div]
  have hf (p : Nat.Primes) : f p≠0 := by
    apply inv_ne_zero
    intro hh
    have hh' := (sub_eq_zero.mp hh).symm
    have he := hn p
    rw [hh',norm_one] at he
    have ht : 1 < (p:ℝ) := by exact_mod_cast p.property.one_lt
    linarith [(div_lt_one (by positivity : 0<(p:ℝ))).mpr ht]
  intro hprod
  have hl := sum_log_of_nonzero_prod f hf hL hprod
  have hz : Summable (fun p : Nat.Primes => z p) := by
    apply Summable.of_norm_bounded_eventually (hl.norm.mul_left 2)
    filter_upwards [hl.norm.tendsto_cofinite_zero.eventually_lt_const zero_lt_one] with p hp
    have h := Complex.norm_exp_sub_one_le (x := -Complex.log (f p)) (by simpa using hp.le)
    rw [norm_neg,Complex.exp_neg,Complex.exp_log (hf p)] at h
    simpa only [f,inv_inv,sub_sub_cancel_left,norm_neg] using h
  exact Nat.Primes.not_summable_one_div (by simpa only [hn] using hz.norm)

theorem solution (w : ℂ) (hr : w.re=1) (hi : w.im≠0) :
    ¬Multipliable (fun p : Nat.Primes => (1-(p:ℂ)^(-w))⁻¹) := by
  rintro ⟨L,hL⟩
  let F (p : ℕ) := (1-(p:ℂ)^(-w))⁻¹
  have hh : HasProd (Set.mulIndicator {p:ℕ | p.Prime} F) L :=
    hasProd_subtype_iff_mulIndicator.mp hL
  have hn : Tendsto (fun n : ℕ => ∏ p ∈ (n+1).primesBelow, F p) atTop (𝓝 L) := by
    have hp := hh.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
    have he (n : ℕ) : (∏ k ∈ Finset.range (n+1),Set.mulIndicator {p:ℕ | p.Prime} F k) =
        ∏ p ∈ (n+1).primesBelow, F p :=
      Finset.prod_mulIndicator_eq_prod_filter _ (fun _ => F) (fun _ => {p:ℕ | p.Prime}) id
    exact hp.congr he
  have hreg := MasulloRH.partialEulerProduct_tendsto_riemannZeta_one_line |w.im| ‖w‖ (abs_pos.mpr hi)
  have hw : w∈{v : ℂ | 1≤v.re ∧ |w.im|≤|v.im| ∧ ‖v‖≤‖w‖} := ⟨hr.ge,le_rfl,le_rfl⟩
  have he := tendsto_nhds_unique hn (hreg.tendsto_at hw)
  exact nonzero_impossible w hr (he ▸ riemannZeta_ne_zero_of_one_le_re hr.ge) hL
