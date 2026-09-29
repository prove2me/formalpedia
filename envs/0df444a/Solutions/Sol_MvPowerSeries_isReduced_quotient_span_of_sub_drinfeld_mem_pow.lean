-- Prove2me | solution 1 for MvPowerSeries.isReduced_quotient_span_of_sub_drinfeld_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1b92ad06-05b4-5740-b7f2-ee8a9b351cb4

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow
import Theorems.Thm_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_isReduced_quotient_span_of_sub_drinfeld_mem_pow

set_option autoImplicit false

open MvPowerSeries

namespace C2

variable {k : Type*} [Field k]

lemma hasSubst_br (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) :
    MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries k), φ] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
    fin_cases s
    · exact PowerSeries.constantCoeff_X
    · exact hφ)

lemma hasSubst_br' (ψ : PowerSeries k) (hψ : PowerSeries.constantCoeff ψ = 0) :
    MvPowerSeries.HasSubst ![ψ, (PowerSeries.X : PowerSeries k)] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
    fin_cases s
    · exact hψ
    · exact PowerSeries.constantCoeff_X)

lemma hasSubst_const_X (i : Fin 2) :
    MvPowerSeries.HasSubst (fun (_ : Unit) => (X i : MvPowerSeries (Fin 2) k)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)

lemma ev_X0 (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ] (X 0 : MvPowerSeries (Fin 2) k) =
      PowerSeries.X := by
  rw [MvPowerSeries.subst_X (hasSubst_br φ hφ)]; rfl

lemma ev_X1 (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ] (X 1 : MvPowerSeries (Fin 2) k) = φ := by
  rw [MvPowerSeries.subst_X (hasSubst_br φ hφ)]; rfl

lemma ev_substX0 (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) (g : PowerSeries k) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ]
      (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) g) = g := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_const_X 0) (hasSubst_br φ hφ)]
  have : (fun (_ : Unit) => MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ]
      (X 0 : MvPowerSeries (Fin 2) k)) = fun _ => (PowerSeries.X : PowerSeries k) := by
    funext u; exact ev_X0 φ hφ
  rw [this, ← PowerSeries.subst_def, PowerSeries.X_subst]

lemma ev_substX1 (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) (g : PowerSeries k) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ]
      (PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) g) = PowerSeries.subst φ g := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_const_X 1) (hasSubst_br φ hφ)]
  have : (fun (_ : Unit) => MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ]
      (X 1 : MvPowerSeries (Fin 2) k)) = fun _ => φ := by
    funext u; exact ev_X1 φ hφ
  rw [this, ← PowerSeries.subst_def]

lemma ev'_X0 (ψ : PowerSeries k) (hψ : PowerSeries.constantCoeff ψ = 0) :
    MvPowerSeries.subst ![ψ, (PowerSeries.X : PowerSeries k)] (X 0 : MvPowerSeries (Fin 2) k) = ψ := by
  rw [MvPowerSeries.subst_X (hasSubst_br' ψ hψ)]; rfl

lemma ev'_X1 (ψ : PowerSeries k) (hψ : PowerSeries.constantCoeff ψ = 0) :
    MvPowerSeries.subst ![ψ, (PowerSeries.X : PowerSeries k)] (X 1 : MvPowerSeries (Fin 2) k) =
      PowerSeries.X := by
  rw [MvPowerSeries.subst_X (hasSubst_br' ψ hψ)]; rfl

lemma ev'_substX0 (ψ : PowerSeries k) (hψ : PowerSeries.constantCoeff ψ = 0) (g : PowerSeries k) :
    MvPowerSeries.subst ![ψ, (PowerSeries.X : PowerSeries k)]
      (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) g) = PowerSeries.subst ψ g := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_const_X 0) (hasSubst_br' ψ hψ)]
  have : (fun (_ : Unit) => MvPowerSeries.subst ![ψ, (PowerSeries.X : PowerSeries k)]
      (X 0 : MvPowerSeries (Fin 2) k)) = fun _ => ψ := by
    funext u; exact ev'_X0 ψ hψ
  rw [this, ← PowerSeries.subst_def]

lemma ev'_substX1 (ψ : PowerSeries k) (hψ : PowerSeries.constantCoeff ψ = 0) (g : PowerSeries k) :
    MvPowerSeries.subst ![ψ, (PowerSeries.X : PowerSeries k)]
      (PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) g) = g := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_const_X 1) (hasSubst_br' ψ hψ)]
  have : (fun (_ : Unit) => MvPowerSeries.subst ![ψ, (PowerSeries.X : PowerSeries k)]
      (X 1 : MvPowerSeries (Fin 2) k)) = fun _ => (PowerSeries.X : PowerSeries k) := by
    funext u; exact ev'_X1 ψ hψ
  rw [this, ← PowerSeries.subst_def, PowerSeries.X_subst]

lemma ker_ev_eq (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) :
    RingHom.ker ((MvPowerSeries.substAlgHom (hasSubst_br φ hφ)).toRingHom :
        MvPowerSeries (Fin 2) k →+* PowerSeries k) =
      Ideal.span {X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ} := by
  apply le_antisymm
  · intro G hG
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.substAlgHom_apply] at hG
    obtain ⟨Q, hQ⟩ :=
      MvPowerSeries.exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero k φ hφ G

    have hrem : MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) k),
        PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ] G =
        PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k)
          (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ] G) := by
      conv_rhs => rw [PowerSeries.subst_def,
        MvPowerSeries.subst_comp_subst_apply (hasSubst_br φ hφ) (hasSubst_const_X 0)]
      congr 1
      funext s
      fin_cases s
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        symm
        exact MvPowerSeries.subst_X (hasSubst_const_X 0) ()
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        rfl
    rw [hrem, hG] at hQ
    have h0 : PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) (0 : PowerSeries k) = 0 := by
      have hX0 : PowerSeries.HasSubst (X 0 : MvPowerSeries (Fin 2) k) :=
        PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)
      have := map_zero (PowerSeries.substAlgHom (R := k) hX0)
      rwa [PowerSeries.coe_substAlgHom] at this
    rw [h0, add_zero] at hQ
    rw [Ideal.mem_span_singleton]
    exact ⟨Q, hQ⟩
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_sub (hasSubst_br φ hφ), ev_X1 φ hφ,
      ev_substX0 φ hφ, sub_self]

lemma isPrime_span_branch (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) :
    (Ideal.span {X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ}).IsPrime := by
  rw [← ker_ev_eq φ hφ]
  exact RingHom.ker_isPrime _

lemma order_branch (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) :
    (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ).order = 1 := by
  classical
  have h1 : ((1 : ℕ) : ℕ∞) = 1 := rfl
  rw [← h1, MvPowerSeries.order_eq_nat]
  refine ⟨⟨Finsupp.single 1 1, ?_, by simp⟩, ?_⟩
  · rw [map_sub, MvPowerSeries.coeff_X, if_pos rfl, PowerSeries.coeff_subst_single]
    have : ¬ (Finsupp.single (1 : Fin 2) 1 = Finsupp.single 0 ((Finsupp.single (1 : Fin 2) 1) 0)) := by
      intro h
      have := congrArg (fun e => e 1) h
      simp at this
    rw [if_neg this]; simp
  · intro d hd
    have hd0 : d = 0 := by
      have : Finsupp.degree d = 0 := by
        have := (Nat.lt_one_iff.mp (by exact_mod_cast hd)); exact this
      exact (Finsupp.degree_eq_zero_iff d).mp this
    subst hd0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, MvPowerSeries.constantCoeff_X,
      PowerSeries.constantCoeff_subst_eq_zero (by simp) φ hφ, sub_zero]

lemma branch_ne_zero (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) :
    (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ) ≠ 0 := by
  intro h
  have := order_branch φ hφ
  rw [h, MvPowerSeries.order_zero] at this
  exact ENat.top_ne_one this

lemma prime_branch (φ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0) :
    Prime (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ) :=
  (Ideal.span_singleton_prime (branch_ne_zero φ hφ)).mp (isPrime_span_branch φ hφ)

lemma finset_prod_dvd_of_prime {M : Type*} [CommMonoidWithZero M] {ι : Type*}
    (s : Finset ι) (p : ι → M) (f : M)
    (hp : ∀ i ∈ s, Prime (p i)) (hdvd : ∀ i ∈ s, p i ∣ f)
    (hnd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ p i ∣ p j) :
    (∏ i ∈ s, p i) ∣ f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hp' : ∀ i ∈ s, Prime (p i) := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hdvd' : ∀ i ∈ s, p i ∣ f := fun i hi => hdvd i (Finset.mem_insert_of_mem hi)
    have hnd' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ p i ∣ p j := fun i hi j hj hij =>
      hnd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    obtain ⟨c, hc⟩ := ih hp' hdvd' hnd'
    have hpa : Prime (p a) := hp a (Finset.mem_insert_self a s)
    have hadvd : p a ∣ (∏ i ∈ s, p i) * c := hc ▸ hdvd a (Finset.mem_insert_self a s)
    rcases hpa.dvd_or_dvd hadvd with h | h
    · obtain ⟨i, hi, hpi⟩ := hpa.exists_mem_finset_dvd h
      exact absurd hpi (hnd a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi)))
    · obtain ⟨c', rfl⟩ := h
      rw [Finset.prod_insert ha, hc]
      exact Dvd.intro c' (by rw [mul_assoc, mul_left_comm])

lemma order_finset_prod {ι : Type*} (s : Finset ι) (p : ι → MvPowerSeries (Fin 2) k) :
    (∏ i ∈ s, p i).order = ∑ i ∈ s, (p i).order := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    by_contra h
    rw [← ne_eq, MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero] at h
    simp at h
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, MvPowerSeries.order_mul, ih]

lemma le_order_of_mem_pow (n : ℕ) :
    ∀ G : MvPowerSeries (Fin 2) k,
      G ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k), X 1}) ^ n → (n : ℕ∞) ≤ G.order := by
  induction n with
  | zero => intro G _; simp
  | succ n ih =>
    intro G hG
    rw [pow_succ'] at hG
    refine Submodule.mul_induction_on hG ?_ ?_
    · intro a ha b hb
      have ha1 : (1 : ℕ∞) ≤ a.order := by
        rw [ENat.one_le_iff_ne_zero, MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero]
        rw [Ideal.mem_span_pair] at ha
        obtain ⟨r, s, rfl⟩ := ha
        simp
      calc ((n + 1 : ℕ) : ℕ∞) = 1 + n := by push_cast; ring
        _ ≤ a.order + b.order := add_le_add ha1 (ih b hb)
        _ ≤ (a * b).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      exact (le_min ha hb).trans MvPowerSeries.min_order_le_add

lemma order_branch' (ψ : PowerSeries k) (hψ : PowerSeries.constantCoeff ψ = 0) :
    (X 0 - PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) ψ).order = 1 := by
  classical
  have h1 : ((1 : ℕ) : ℕ∞) = 1 := rfl
  rw [← h1, MvPowerSeries.order_eq_nat]
  refine ⟨⟨Finsupp.single 0 1, ?_, by simp⟩, ?_⟩
  · rw [map_sub, MvPowerSeries.coeff_X, if_pos rfl, PowerSeries.coeff_subst_single]
    have : ¬ (Finsupp.single (0 : Fin 2) 1 = Finsupp.single 1 ((Finsupp.single (0 : Fin 2) 1) 1)) := by
      intro h
      have := congrArg (fun e => e 0) h
      simp at this
    rw [if_neg this]; simp
  · intro d hd
    have hd0 : d = 0 := by
      have : Finsupp.degree d = 0 := by
        have := (Nat.lt_one_iff.mp (by exact_mod_cast hd)); exact this
      exact (Finsupp.degree_eq_zero_iff d).mp this
    subst hd0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, MvPowerSeries.constantCoeff_X,
      PowerSeries.constantCoeff_subst_eq_zero (by simp) ψ hψ, sub_zero]

lemma coeff_one_subst_of_sq_dvd (φ ψ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ0 : PowerSeries.constantCoeff ψ = 0) (hψ1 : PowerSeries.coeff 1 ψ = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst φ ψ) = 0 := by
  have hX2 : (PowerSeries.X : PowerSeries k) ^ 2 ∣ ψ := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simpa using hψ0
    · exact hψ1
  obtain ⟨ψ₂, rfl⟩ := hX2
  have ha : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ
  rw [PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]
  obtain ⟨φ₁, rfl⟩ := PowerSeries.X_dvd_iff.mpr hφ
  have : (PowerSeries.X : PowerSeries k) ^ 2 ∣ (PowerSeries.X * φ₁) ^ 2 * PowerSeries.subst (PowerSeries.X * φ₁) ψ₂ :=
    ⟨φ₁ ^ 2 * PowerSeries.subst (PowerSeries.X * φ₁) ψ₂, by ring⟩
  exact (PowerSeries.X_pow_dvd_iff.mp this) 1 (by norm_num)

lemma coeff_one_subst_of_sq_dvd' (φ ψ : PowerSeries k) (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ0 : PowerSeries.constantCoeff ψ = 0) (hψ1 : PowerSeries.coeff 1 ψ = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst ψ φ) = 0 := by
  have hX2 : (PowerSeries.X : PowerSeries k) ^ 2 ∣ ψ := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simpa using hψ0
    · exact hψ1
  obtain ⟨φ₁, rfl⟩ := PowerSeries.X_dvd_iff.mpr hφ
  have ha : PowerSeries.HasSubst ψ := PowerSeries.HasSubst.of_constantCoeff_zero' hψ0
  rw [PowerSeries.subst_mul ha, PowerSeries.subst_X ha]
  obtain ⟨ψ₂, hψ₂⟩ := hX2
  have : (PowerSeries.X : PowerSeries k) ^ 2 ∣ ψ * PowerSeries.subst ψ φ₁ :=
    ⟨ψ₂ * PowerSeries.subst ψ φ₁, by rw [hψ₂]; ring⟩
  exact (PowerSeries.X_pow_dvd_iff.mp this) 1 (by norm_num)

end C2

open C2 in

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] (hq : (q : k) = 0)
    (f : MvPowerSeries (Fin 2) k)
    (hf : f - (X 0 * X 1 ^ q - X 0 ^ q * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k), X 1}) ^ (q + 2)) :
    IsReduced (MvPowerSeries (Fin 2) k ⧸ Ideal.span {f}) := by
  classical
  have hqp : q.Prime := Fact.out

  haveI : CharP k q := (CharP.charP_iff_prime_eq_zero hqp).mpr hq
  set a : ZMod q →+* k := ZMod.castHom (dvd_refl q) k with ha_def
  have ha : ∀ i : ZMod q, (a i) ^ q = a i := fun i => by rw [← map_pow, ZMod.pow_card]
  have hainj : Function.Injective a := a.injective

  have hbr : ∀ i : ZMod q, ∃ φ : PowerSeries k, PowerSeries.constantCoeff φ = 0 ∧
      PowerSeries.coeff 1 φ = a i ∧ MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ] f = 0 :=
    fun i => MvPowerSeries.exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow q k hq f hf (a i) (ha i)
  choose φ hφ0 hφ1 hφroot using hbr
  set L : ZMod q → MvPowerSeries (Fin 2) k :=
    fun i => X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) (φ i) with hL
  have hLdvd : ∀ i, L i ∣ f := by
    intro i
    have : f ∈ RingHom.ker ((MvPowerSeries.substAlgHom (hasSubst_br (φ i) (hφ0 i))).toRingHom :
        MvPowerSeries (Fin 2) k →+* PowerSeries k) := by
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.substAlgHom_apply]
      exact hφroot i
    rw [ker_ev_eq (φ i) (hφ0 i), Ideal.mem_span_singleton] at this
    exact this

  set sw : MvPowerSeries (Fin 2) k ≃ₐ[k] MvPowerSeries (Fin 2) k :=
    MvPowerSeries.renameEquiv k (Equiv.swap (0 : Fin 2) 1) with hsw
  have hsw_apply : ∀ x, sw x = MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) x := fun x => rfl
  have hswX0 : sw (X 0) = X 1 := by rw [hsw_apply, MvPowerSeries.rename_X]; rfl
  have hswX1 : sw (X 1) = X 0 := by rw [hsw_apply, MvPowerSeries.rename_X]; rfl
  have hswsw : ∀ x, sw (sw x) = x := by
    intro x
    have : sw.symm = sw := by
      rw [hsw, MvPowerSeries.renameEquiv_symm, Equiv.symm_swap]
    conv_lhs => rw [← this]
    exact sw.symm_apply_apply x
  set 𝔫 : Ideal (MvPowerSeries (Fin 2) k) := Ideal.span {(X 0 : MvPowerSeries (Fin 2) k), X 1} with h𝔫
  have hsw𝔫 : 𝔫.map sw = 𝔫 := by
    rw [h𝔫, Ideal.map_span, Set.image_pair, hswX0, hswX1, Ideal.span_pair_comm]
  set Φ : MvPowerSeries (Fin 2) k := X 0 * X 1 ^ q - X 0 ^ q * X 1 with hΦ
  have hswΦ : sw Φ = -Φ := by
    rw [hΦ, map_sub, map_mul, map_mul, map_pow, map_pow, hswX0, hswX1]; ring
  set g : MvPowerSeries (Fin 2) k := -(sw f) with hg
  have hgΦ : g - Φ ∈ 𝔫 ^ (q + 2) := by
    have h1 : g - Φ = -(sw (f - Φ)) := by rw [map_sub, hswΦ, hg]; ring
    rw [h1]
    refine neg_mem ?_
    have := Ideal.mem_map_of_mem sw hf
    rwa [Ideal.map_pow, hsw𝔫] at this
  obtain ⟨ψ, hψ0, hψ1, hψroot⟩ :=
    MvPowerSeries.exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow q k hq g hgΦ 0
      (by rw [zero_pow hqp.ne_zero])
  set Lψ : MvPowerSeries (Fin 2) k := X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) ψ with hLψ
  set Linf : MvPowerSeries (Fin 2) k := X 0 - PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) ψ with hLinf
  have hswsubst : sw (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) ψ) =
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) ψ := by
    rw [hsw_apply, MvPowerSeries.rename_eq_subst, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply (hasSubst_const_X 0) (MvPowerSeries.HasSubst.X_comp _),
      PowerSeries.subst_def]
    congr 1
    funext u
    rw [MvPowerSeries.subst_X (MvPowerSeries.HasSubst.X_comp _)]
    rfl
  have hswL : sw Lψ = Linf := by
    rw [hLψ, map_sub, hswX1, hswsubst]
  have hLinfdvd : Linf ∣ f := by
    have hgmem : g ∈ RingHom.ker ((MvPowerSeries.substAlgHom (hasSubst_br ψ hψ0)).toRingHom :
        MvPowerSeries (Fin 2) k →+* PowerSeries k) := by
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.substAlgHom_apply]
      exact hψroot
    rw [ker_ev_eq ψ hψ0, Ideal.mem_span_singleton] at hgmem
    obtain ⟨Q, hQ⟩ := hgmem
    have hf' : f = Linf * (-(sw Q)) := by
      have : f = -(sw g) := by rw [hg, map_neg, hswsw, neg_neg]
      rw [this, hQ, map_mul, hswL]; ring
    exact ⟨_, hf'⟩
  have hLinfprime_ideal : (Ideal.span {Linf}).IsPrime := by
    have : (Ideal.span {Lψ}).map sw = Ideal.span {Linf} := by
      rw [Ideal.map_span, Set.image_singleton, hswL]
    rw [← this]
    haveI := isPrime_span_branch (k := k) ψ hψ0
    exact Ideal.map_isPrime_of_equiv sw
  have hLinfne : Linf ≠ 0 := by
    intro h
    have := order_branch' (k := k) ψ hψ0
    rw [← hLinf, h, MvPowerSeries.order_zero] at this
    exact ENat.top_ne_one this
  have hLinfprime : Prime Linf := (Ideal.span_singleton_prime hLinfne).mp hLinfprime_ideal

  set p : Option (ZMod q) → MvPowerSeries (Fin 2) k := fun o => Option.elim o Linf L with hp
  have hp_none : p none = Linf := rfl
  have hp_some : ∀ i, p (some i) = L i := fun i => rfl
  have hpprime : ∀ o, Prime (p o) := by
    rintro (_ | i)
    · exact hLinfprime
    · rw [hp_some]; exact prime_branch (φ i) (hφ0 i)
  have hpdvd : ∀ o, p o ∣ f := by
    rintro (_ | i)
    · exact hLinfdvd
    · exact hLdvd i

  have hev_kill : ∀ (i : ZMod q) (x : MvPowerSeries (Fin 2) k), L i ∣ x →
      MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ i] x = 0 := by
    intro i x hx
    obtain ⟨c, rfl⟩ := hx
    rw [MvPowerSeries.subst_mul (hasSubst_br (φ i) (hφ0 i)), hL]
    simp only []
    rw [MvPowerSeries.subst_sub (hasSubst_br (φ i) (hφ0 i)), ev_X1 (φ i) (hφ0 i),
      ev_substX0 (φ i) (hφ0 i), sub_self, zero_mul]
  have hev'_kill : ∀ x : MvPowerSeries (Fin 2) k, Linf ∣ x →
      MvPowerSeries.subst ![ψ, (PowerSeries.X : PowerSeries k)] x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := hx
    rw [MvPowerSeries.subst_mul (hasSubst_br' ψ hψ0), hLinf,
      MvPowerSeries.subst_sub (hasSubst_br' ψ hψ0), ev'_X0 ψ hψ0, ev'_substX1 ψ hψ0, sub_self, zero_mul]
  have hnd : ∀ o o' : Option (ZMod q), o ≠ o' → ¬ p o ∣ p o' := by
    rintro (_ | i) (_ | j) hne hdvd
    · exact hne rfl
    ·
      have h := hev'_kill (L j) hdvd
      rw [hL] at h
      simp only [] at h
      rw [MvPowerSeries.subst_sub (hasSubst_br' ψ hψ0), ev'_X1 ψ hψ0, ev'_substX0 ψ hψ0] at h
      have h1 := congrArg (PowerSeries.coeff 1) h
      rw [map_sub, PowerSeries.coeff_one_X, coeff_one_subst_of_sq_dvd' (φ j) ψ (hφ0 j) hψ0 hψ1,
        map_zero] at h1
      norm_num at h1
    ·
      have h := hev_kill i Linf hdvd
      rw [hLinf, MvPowerSeries.subst_sub (hasSubst_br (φ i) (hφ0 i)), ev_X0 (φ i) (hφ0 i),
        ev_substX1 (φ i) (hφ0 i)] at h
      have h1 := congrArg (PowerSeries.coeff 1) h
      rw [map_sub, PowerSeries.coeff_one_X, coeff_one_subst_of_sq_dvd (φ i) ψ (hφ0 i) hψ0 hψ1,
        map_zero] at h1
      norm_num at h1
    ·
      have h := hev_kill i (L j) hdvd
      rw [hL] at h
      simp only [] at h
      rw [MvPowerSeries.subst_sub (hasSubst_br (φ i) (hφ0 i)), ev_X1 (φ i) (hφ0 i),
        ev_substX0 (φ i) (hφ0 i), sub_eq_zero] at h
      have h1 := congrArg (PowerSeries.coeff 1) h
      rw [hφ1 i, hφ1 j] at h1
      exact hne (congrArg some (hainj h1))

  have hPdvd : (∏ o, p o) ∣ f :=
    finset_prod_dvd_of_prime Finset.univ p f (fun o _ => hpprime o) (fun o _ => hpdvd o)
      (fun o _ o' _ hne => hnd o o' hne)
  obtain ⟨c, hc⟩ := hPdvd

  have hporder : ∀ o, (p o).order = 1 := by
    rintro (_ | i)
    · exact order_branch' ψ hψ0
    · exact order_branch (φ i) (hφ0 i)
  have hProd_order : (∏ o, p o).order = (q + 1 : ℕ) := by
    rw [order_finset_prod, Finset.sum_congr rfl (fun o _ => hporder o), Finset.sum_const,
      Finset.card_univ, Fintype.card_option, ZMod.card, nsmul_eq_mul, mul_one]
  have hforder : f.order = (q + 1 : ℕ) := by
    set e₁ : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 q with he₁
    set e₂ : Fin 2 →₀ ℕ := Finsupp.single 0 q + Finsupp.single 1 1 with he₂
    have hΦmon : Φ = MvPowerSeries.monomial e₁ 1 - MvPowerSeries.monomial e₂ 1 := by
      rw [hΦ, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.X_def, MvPowerSeries.X_def,
        MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial, mul_one]
    have hcoeffΦ : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d Φ =
        (if d = e₁ then 1 else 0) - (if d = e₂ then 1 else 0) := by
      intro d
      rw [hΦmon, map_sub, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
    have hdeg₁ : Finsupp.degree e₁ = q + 1 := by
      rw [he₁, map_add, Finsupp.degree_single, Finsupp.degree_single]; ring
    have hdeg₂ : Finsupp.degree e₂ = q + 1 := by
      rw [he₂, map_add, Finsupp.degree_single, Finsupp.degree_single]
    have hne₁₂ : e₁ ≠ e₂ := by
      intro h
      have := congrArg (fun e => e 0) h
      simp [he₁, he₂] at this
      exact hqp.ne_one this.symm
    have hGorder : ((q + 2 : ℕ) : ℕ∞) ≤ (f - Φ).order := le_order_of_mem_pow (q + 2) (f - Φ) hf
    have hfeq : f = Φ + (f - Φ) := by ring
    have hcoeff_f : ∀ d : Fin 2 →₀ ℕ, Finsupp.degree d < q + 2 →
        MvPowerSeries.coeff d f = MvPowerSeries.coeff d Φ := by
      intro d hd
      have hG0 : MvPowerSeries.coeff d (f - Φ) = 0 :=
        MvPowerSeries.coeff_of_lt_order (f := f - Φ) (lt_of_lt_of_le (by exact_mod_cast hd) hGorder)
      rw [map_sub, sub_eq_zero] at hG0
      exact hG0
    rw [MvPowerSeries.order_eq_nat]
    refine ⟨⟨e₁, ?_, hdeg₁⟩, ?_⟩
    · rw [hcoeff_f e₁ (by rw [hdeg₁]; omega), hcoeffΦ, if_pos rfl, if_neg hne₁₂]
      norm_num
    · intro d hd
      rw [hcoeff_f d (by omega), hcoeffΦ]
      have h1 : d ≠ e₁ := fun h => by rw [h, hdeg₁] at hd; exact lt_irrefl _ hd
      have h2 : d ≠ e₂ := fun h => by rw [h, hdeg₂] at hd; exact lt_irrefl _ hd
      rw [if_neg h1, if_neg h2, sub_zero]
  have hcorder : c.order = 0 := by
    by_contra hne
    have h1 : (1 : ℕ∞) ≤ c.order := ENat.one_le_iff_ne_zero.mpr hne
    have := hforder
    rw [hc, MvPowerSeries.order_mul, hProd_order] at this
    have h2 : ((q + 1 : ℕ) : ℕ∞) + 1 ≤ ((q + 1 : ℕ) : ℕ∞) + c.order := add_le_add le_rfl h1
    rw [this] at h2
    have h3 : ((q + 1 : ℕ) : ℕ∞) + 1 ≤ ((q + 1 : ℕ) : ℕ∞) + 0 := by simpa using h2
    have h4 := (WithTop.add_le_add_iff_left (WithTop.natCast_ne_top (q + 1))).mp h3
    have h5 : (1 : ℕ∞) ≤ 0 := h4
    exact absurd h5 (by decide)
  have hcunit : IsUnit c := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    intro h0
    have : c.order ≠ 0 := MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr h0
    exact this hcorder

  have hfdvdP : f ∣ ∏ o, p o := by
    refine ⟨↑(hcunit.unit⁻¹), ?_⟩
    rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [← Ideal.isRadical_iff_quotient_reduced]
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  have hpx : ∀ o, p o ∣ x := fun o => (hpprime o).dvd_of_dvd_pow ((hpdvd o).trans hn)
  have hPx : (∏ o, p o) ∣ x :=
    finset_prod_dvd_of_prime Finset.univ p x (fun o _ => hpprime o) (fun o _ => hpx o)
      (fun o _ o' _ hne => hnd o o' hne)
  exact hfdvdP.trans hPx

end S_MvPowerSeries_isReduced_quotient_span_of_sub_drinfeld_mem_pow
end P2MW
export P2MW.S_MvPowerSeries_isReduced_quotient_span_of_sub_drinfeld_mem_pow (solution)
