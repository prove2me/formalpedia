-- Prove2me | solution 1 for IntConeFPT.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T08:44:52.900845+00:00
-- url     : https://prove2.me/submissions/8c186d6a-8b28-462d-a540-ab8d7fddea19

import Theorems.Thm_IntConeFPT_short_recession_step
import Theorems.Thm_IntConeFPT_sparse_perspective_projection
import Theorems.Thm_IntConeFPT_lemma_7

open IntConeFPT
namespace IntConeFPT.CountPeeling

private lemma convex_P (I : Instance) (t : Fin I.τ) : Convex ℝ (I.P t) := by
  intro p hp q hq a b ha hb hab i
  have hpi := hp i
  have hqi := hq i
  have hsum :
      (∑ j, (I.Aloc t i j : ℝ) * (a • p + b • q).1 j) +
      (∑ j, (I.Bloc t i j : ℝ) * (a • p + b • q).2 j) =
      a * ((∑ j, (I.Aloc t i j : ℝ) * p.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p.2 j)) +
      b * ((∑ j, (I.Aloc t i j : ℝ) * q.1 j) + (∑ j, (I.Bloc t i j : ℝ) * q.2 j)) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_left_comm, ← Finset.mul_sum]
    ring
  rw [hsum]
  calc
    _ ≤ a * (I.bloc t i : ℝ) + b * (I.bloc t i : ℝ) := add_le_add (mul_le_mul_of_nonneg_left hpi ha) (mul_le_mul_of_nonneg_left hqi hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

private lemma discreteJensen_X (I : Instance) (hI : I.Valid) (t : Fin I.τ) :
    DiscreteJensen {x : Fin I.d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' I.P t}
      (fun x => I.f t (fun i => (x i : ℝ))) := by
  intro x _ m θ xs hxs hθ0 hθ1 hx_eq
  have hconv := hI.convex t
  have hle := hconv.map_sum_le (fun i _ => hθ0 i) hθ1 (fun i _ => hxs i)
  rw [← hx_eq] at hle
  simpa only [smul_eq_mul] using hle

private lemma exists_global_opt_of_bdd_below (I : Instance)
    (hfeas : ∃ μ, I.Feasible μ)
    (hbdd : ∃ L : ℝ, ∀ μ, I.Feasible μ → L ≤ I.cost μ) :
    ∃ μ_opt : Mult I, I.Feasible μ_opt ∧ ∀ μ : Mult I, I.Feasible μ → I.cost μ_opt ≤ I.cost μ := by
  obtain ⟨L, hL⟩ := hbdd
  let Q_den : ℕ := ∏ t : Fin I.τ, ∏ j : Fin (monomials I.d (I.deg t)).length, (I.coeff t j).den
  have hQ_pos : 0 < Q_den := by
    refine Finset.prod_pos fun t _ => Finset.prod_pos fun j _ => (I.coeff t j).pos
  let coeffZ : (t : Fin I.τ) → Fin (monomials I.d (I.deg t)).length → ℤ := fun t j =>
    (I.coeff t j).num * ((Q_den / (I.coeff t j).den : ℕ) : ℤ)
  have hcoeff_eq : ∀ t j, (coeffZ t j : ℝ) = (Q_den : ℝ) * (I.coeff t j : ℝ) := by
    intro t j
    have hdvd : (I.coeff t j).den ∣ Q_den :=
      dvd_trans (Finset.dvd_prod_of_mem (fun j => (I.coeff t j).den) (Finset.mem_univ j))
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ t))
    have hmul_den : ((Q_den / (I.coeff t j).den : ℕ) : ℝ) * ((I.coeff t j).den : ℝ) = (Q_den : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hden_ne : ((I.coeff t j).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (I.coeff t j).pos.ne'
    have hq_eq : (I.coeff t j : ℝ) = ((I.coeff t j).num : ℝ) / ((I.coeff t j).den : ℝ) := by
      rw [Rat.cast_def]
    calc (coeffZ t j : ℝ)
      _ = ((I.coeff t j).num : ℝ) * ((Q_den / (I.coeff t j).den : ℕ) : ℝ) := by
          simp only [coeffZ, Int.cast_mul, Int.cast_natCast]
      _ = ((I.coeff t j).num : ℝ) * ((Q_den : ℝ) / ((I.coeff t j).den : ℝ)) := by
          rw [(eq_div_iff hden_ne).mpr hmul_den]
      _ = (Q_den : ℝ) * (((I.coeff t j).num : ℝ) / ((I.coeff t j).den : ℝ)) := by ring
      _ = (Q_den : ℝ) * (I.coeff t j : ℝ) := by rw [← hq_eq]
  have hcost_int : ∀ μ : Mult I, ∃ z : ℤ, (Q_den : ℝ) * I.cost μ = (z : ℝ) := by
    intro μ
    let fZ : (t : Fin I.τ) → (Fin I.d → ℤ) → ℤ := fun t x =>
      ∑ j : Fin (monomials I.d (I.deg t)).length,
        coeffZ t j * ∏ i, x i ^ ((monomials I.d (I.deg t)).get j i)
    refine ⟨∑ t : Fin I.τ, (μ t).sum fun g n => (n : ℤ) * fZ t g.1, ?_⟩
    unfold Instance.cost costOf
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hf_eq : (Q_den : ℝ) * ((μ t g : ℝ) * I.f t (fun i => (g.1 i : ℝ))) =
        (μ t g : ℝ) * (fZ t g.1 : ℝ) := by
      rw [mul_left_comm]
      congr 1
      simp only [fZ, Instance.f, Finset.mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_prod,
        Int.cast_pow, hcoeff_eq]
      refine Finset.sum_congr rfl fun j _ => by ring
    exact hf_eq
  let P_int : ℤ → Prop := fun z => ∃ μ, I.Feasible μ ∧ (Q_den : ℝ) * I.cost μ = (z : ℝ)
  have hP_bdd : ∃ b : ℤ, ∀ z : ℤ, P_int z → b ≤ z := by
    refine ⟨Int.floor ((Q_den : ℝ) * L), fun z ⟨μ, hμ, hμ_eq⟩ => ?_⟩
    have h1 : (Q_den : ℝ) * L ≤ (Q_den : ℝ) * I.cost μ :=
      mul_le_mul_of_nonneg_left (hL μ hμ) (Nat.cast_nonneg _)
    rw [hμ_eq] at h1
    exact_mod_cast (Int.floor_le _).trans h1
  have hP_inh : ∃ z : ℤ, P_int z := by
    obtain ⟨μ₀, hμ₀⟩ := hfeas
    obtain ⟨z₀, hz₀⟩ := hcost_int μ₀
    exact ⟨z₀, μ₀, hμ₀, hz₀⟩
  obtain ⟨z_min, ⟨μ_opt, hμ_opt, hμ_opt_eq⟩, hz_min⟩ := Int.exists_least_of_bdd hP_bdd hP_inh
  refine ⟨μ_opt, hμ_opt, fun μ hμ => ?_⟩
  obtain ⟨z, hz⟩ := hcost_int μ
  have hz_le : (z_min : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_min z ⟨μ, hμ, hz⟩
  rw [← hμ_opt_eq, ← hz] at hz_le
  exact le_of_mul_le_mul_left hz_le (Nat.cast_pos.mpr hQ_pos)

private lemma nstar_mono_bound (I : Instance) (U : ℕ) (hU : 1 ≤ U)
    {p : ℕ} (hp_le : p ≤ I.τ * 2 ^ I.d) :
    p * (p + 1) * p.factorial * ((I.τ * 2 ^ I.d * I.k + 1).factorial * U ^ (I.τ * 2 ^ I.d * I.k + 1)) ^ p ≤
      Nstar I.τ I.d I.k U := by
  let s := I.τ * 2 ^ I.d
  let H := (s * I.k + 1).factorial * U ^ (s * I.k + 1)
  have hH1 : 1 ≤ H := Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos hU)
  change p * (p + 1) * p.factorial * H ^ p ≤ s * (s + 1) * s.factorial * H ^ s
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul hp_le (Nat.add_le_add_right hp_le 1)) (Nat.factorial_le hp_le))
    (Nat.pow_le_pow_right hH1 hp_le)

private abbrev lhs {p m : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (z : Fin p → ℕ) (i : Fin m) :=
  ∑ j, A i j * (z j : ℤ)

private abbrev price {p : ℕ} (c : Fin p → ℝ) (z : Fin p → ℕ) := ∑ j, (z j : ℝ) * c j

private lemma price_add {p : ℕ} (c : Fin p → ℝ) (y r : Fin p → ℕ) :
    price c (y+r) = price c y + price c r := by simp [price, add_mul, Finset.sum_add_distrib]

private lemma lhs_add {p m : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (y r : Fin p → ℕ) (i : Fin m) :
    lhs A (y+r) i = lhs A y i + lhs A r i := by simp [lhs, mul_add, Finset.sum_add_distrib]

private lemma peel {p m H : ℕ} (hp : 1 ≤ p) (hH : 1 ≤ H)
    (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ H) (hb : ∀ i, |b i| ≤ H)
    (c : Fin p → ℝ) (z : Fin p → ℕ) (hz : ∀ i, lhs A z i ≤ b i) :
    let B := p * (p+1) * p.factorial * H ^ p
    (∃ y, (∀ i, lhs A y i ≤ b i) ∧ (∑ j, y j) ≤ B ∧ price c y ≤ price c z) ∨
    (∃ r, (∀ i, lhs A r i ≤ 0) ∧ (∑ j, r j) ≤ B ∧ price c r < 0) := by
  intro B
  by_cases h : (∑ j, z j) ≤ B
  · exact Or.inl ⟨z, hz, h, le_rfl⟩
  obtain ⟨y,r,he,hy,hr,hrpos,hrle⟩ := short_recession_step hp hH A b hA hb z hz (lt_of_not_ge h)
  by_cases hn : price c r < 0
  · exact Or.inr ⟨r,hr,hrle,hn⟩
  have hylt : (∑ j, y j) < ∑ j, z j := by simpa [he, Finset.sum_add_distrib]
  rcases peel hp hH A b hA hb c y hy with ⟨y',hy',hsize,hcost⟩ | ray
  · exact Or.inl ⟨y',hy',hsize,hcost.trans (by rw [he, price_add]; linarith)⟩
  · exact Or.inr ray
termination_by ∑ j, z j

private lemma sparse (I : Instance) (hI : I.Valid) (μ : Mult I) (hs : I.Supported μ) :
    ∃ ν : Mult I, I.Supported ν ∧ (∀ t, I.typeAgg ν t = I.typeAgg μ t) ∧
      I.cost ν ≤ I.cost μ ∧ (∑ t, (ν t).support.card) ≤ I.τ * 2 ^ I.d := by
  obtain ⟨ν, hv, ha, hc, _, hsiz⟩ :=
    lemma_7 hI.one_le_d I.P (convex_P I) hI.bounded I.f (discreteJensen_X I hI) μ hs
  exact ⟨ν,hv,fun t => by simp [Instance.typeAgg, (ha t).1, (ha t).2],
    Finset.sum_le_sum (fun t _ => hc t),hsiz⟩

-- For a bounded optimum the 'negative ray' branch contradicts optimality after lifting z+r.
-- For a homogeneous problem the ray itself is a feasible witness.
private lemma compress (I : Instance) (hI : I.Valid) (M U : ℕ)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (hU : 1 ≤ U) (D : IntDesc I)
    (hD : D.Describes) (hDU : D.BoundedBy M U)
    (rhs : Fin D.mW → ℤ) (hrhs : ∀ i, |rhs i| ≤ U)
    (μ : Mult I) (hs : I.Supported μ)
    (ha : ∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ rhs i)
    (mode : Fin 3)
    (hopt : mode = 1 → ∀ ν : Mult I, I.Supported ν →
      (∀ i, D.aggLHS (fun t => I.typeAgg ν t) i ≤ rhs i) → I.cost μ ≤ I.cost ν)
    (hhom : mode = 2 → rhs = 0 ∧ I.cost μ < 0) :
    ∃ ν : Mult I, I.Supported ν ∧ (∀ i, D.aggLHS (fun t => I.typeAgg ν t) i ≤ rhs i) ∧
      I.totalCount ν ≤ Nstar I.τ I.d I.k U ∧
      (mode = 1 → I.cost ν ≤ I.cost μ) ∧ (mode = 2 → I.cost ν < 0) := by
  obtain ⟨v,vs,va,vc,vsiz⟩ := sparse I hI μ hs
  have vagg : ∀ i, D.aggLHS (fun t => I.typeAgg v t) i ≤ rhs i := by simpa only [va] using ha
  by_cases hcnt : I.totalCount v = 0
  · exact ⟨v,vs,vagg,hcnt ▸ Nat.zero_le _,fun _ => vc,fun e => vc.trans_lt (hhom e).2⟩
  obtain ⟨p,m,A,b,c,z,hp,hps,hA,hb,hb0,hz,hzc,lift⟩ :=
    sparse_perspective_projection I hI M U hbox hU D hD hDU v vs vsiz (Nat.pos_of_ne_zero hcnt)
      rhs hrhs vagg
  let H := (I.τ * 2^I.d * I.k + 1).factorial * U ^ (I.τ * 2^I.d * I.k + 1)
  have hH : 1 ≤ H := Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos hU)
  have hn := nstar_mono_bound I U hU hps
  let w : Fin p → ℝ := if mode = 0 then 0 else c
  rcases peel hp hH A b hA hb w z hz with ⟨y,hy,hyN,hyc⟩ | ⟨r,hr,hrN,hrc⟩
  · obtain ⟨ν,hν,hνa,hνn,hνc⟩ := lift y hy
    refine ⟨ν,hν,hνa,hνn ▸ hyN.trans hn,?_,?_⟩
    · intro e
      have he : w = c := by simp [w,e]
      rw [he] at hyc
      exact hνc.le.trans (hyc.trans (hzc.le.trans vc))
    · intro e
      have he : w = c := by simp [w,e]
      rw [he] at hyc
      exact (hνc.le.trans (hyc.trans (hzc.le.trans vc))).trans_lt (hhom e).2
  · by_cases h0 : mode = 0
    · simp [w,h0,price] at hrc
    have he : w = c := if_neg h0
    rw [he] at hrc
    by_cases h1 : mode = 1
    · obtain ⟨ν,hν,hνa,_,hcost⟩ := lift (z+r) (fun i => by
        change lhs A (z+r) i ≤ _
        rw [lhs_add]; linarith [hz i, hr i])
      have hbad := hopt h1 ν hν hνa
      change I.cost ν = price c (z+r) at hcost
      change price c z = I.cost v at hzc
      rw [price_add, hzc] at hcost
      linarith
    have h2 : mode = 2 := by fin_cases mode <;> simp_all
    obtain ⟨ν,hν,hνa,hνn,hνc⟩ := lift r (fun i => by simpa [hb0 (hhom h2).1] using hr i)
    exact ⟨ν,hν,hνa,hνn ▸ hrN.trans hn,fun e => (h1 e).elim,fun _ => hνc.trans_lt hrc⟩

end IntConeFPT.CountPeeling
open IntConeFPT.CountPeeling

theorem solution (I : Instance) (hI : I.Valid) (M U : ℕ) (hM : 1 ≤ M)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (hU : 1 ≤ U) (D : IntDesc I) (hD : D.Describes)
    (hDU : D.BoundedBy M U) :
    ((∃ μ, I.Feasible μ) → ∃ μ, I.Feasible μ ∧ I.totalCount μ ≤ Nstar I.τ I.d I.k U) ∧
    ((∃ μ, I.Feasible μ) → (∃ L : ℝ, ∀ μ, I.Feasible μ → L ≤ I.cost μ) →
      ∃ μ, I.Feasible μ ∧ I.totalCount μ ≤ Nstar I.τ I.d I.k U ∧
        ∀ μ', I.Feasible μ' → I.cost μ ≤ I.cost μ') ∧
    ((∃ μ, I.Supported μ ∧ (∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ 0) ∧ I.cost μ < 0) →
      ∃ μ, I.Supported μ ∧ (∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ 0) ∧ I.cost μ < 0 ∧
        I.totalCount μ ≤ Nstar I.τ I.d I.k U) := by
  have comp := compress I hI M U hbox hU D hD hDU
  have feas (v : Mult I) : I.Feasible v ↔ I.Supported v ∧
      ∀ i, D.aggLHS (fun t => I.typeAgg v t) i ≤ D.cW i := by
    exact and_congr_right' (hD.1 (fun t => I.typeAgg v t)).symm
  refine ⟨?_,?_,?_⟩
  · rintro ⟨μ,hμ⟩
    obtain ⟨ν,hs,ha,hN,_,_⟩ := comp D.cW hDU.2.2.2.1 μ hμ.1
      (((feas μ).mp hμ).2) 0 (by intro h; contradiction) (by intro h; contradiction)
    exact ⟨ν,(feas ν).mpr ⟨hs,ha⟩,hN⟩
  · intro hf hb
    obtain ⟨μ,hμ,ho⟩ := exists_global_opt_of_bdd_below I hf hb
    obtain ⟨ν,hs,ha,hN,hc,_⟩ := comp D.cW hDU.2.2.2.1 μ hμ.1 (((feas μ).mp hμ).2) 1
      (fun _ v vs va => ho v ((feas v).mpr ⟨vs,va⟩)) (by intro h; contradiction)
    exact ⟨ν,(feas ν).mpr ⟨hs,ha⟩,hN,fun v hv => (hc rfl).trans (ho v hv)⟩
  · rintro ⟨μ,hs,ha,hc⟩
    obtain ⟨ν,vs,va,hN,_,vn⟩ := comp 0 (by simp) μ hs (by simpa using ha) 2
      (by intro h; contradiction) (fun _ => ⟨rfl,hc⟩)
    exact ⟨ν,vs,by simpa using va,vn rfl,hN⟩
