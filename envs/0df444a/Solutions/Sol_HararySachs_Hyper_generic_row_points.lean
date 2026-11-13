-- Prove2me | solution 1 for HararySachs.Hyper.generic_row_points
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:30:54.075891+00:00
-- url     : https://prove2.me/submissions/25fefe58-a2dc-4d39-a091-d77d8c753598

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Theorems.Thm_MvResultant_poisson_block
import Theorems.Thm_MvResultant_isWeightedHomogeneous_block
import Theorems.Thm_MvResultant_blockDegree_le
import Theorems.Thm_MvResultant_blockDegree_ge

open HararySachs.Hyper MvPolynomial Finset

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace GenPtsAux

variable {n k : ℕ}

/-! ### Resultants of systems over an arbitrary commutative ring -/

/-- the resultant of a system of forms with coefficients in `S` -/
noncomputable def resF {S : Type*} [CommRing S] (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (G : Fin n → MvPolynomial (Fin n) S) : S :=
  aeval (fun v : ResVar n (fun _ => k - 1) => coeff v.2.1 (G v.1))
    (MvPolynomial.map (Int.castRingHom S) res)

lemma resF_eq_eval₂ {S : Type*} [CommRing S] (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (G : Fin n → MvPolynomial (Fin n) S) :
    resF res G = eval₂ (Int.castRingHom S)
      (fun v : ResVar n (fun _ => k - 1) => coeff v.2.1 (G v.1)) res := by
  unfold resF
  rw [aeval_def, eval₂_map]
  congr 1

lemma resF_map {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (G : Fin n → MvPolynomial (Fin n) S) :
    φ (resF res G) = resF res (fun j => MvPolynomial.map φ (G j)) := by
  rw [resF_eq_eval₂, resF_eq_eval₂, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

lemma map_update {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (G : Fin n → MvPolynomial (Fin n) S) (i : Fin n) (g : MvPolynomial (Fin n) S) :
    (fun j => MvPolynomial.map φ (Function.update G i g j)) =
      Function.update (fun j => MvPolynomial.map φ (G j)) i (MvPolynomial.map φ g) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- the degree bound for a resultant whose block-`i` coefficients have degree `≤ 1` -/
lemma natDegree_eval₂_le {σ : Type*} (P : MvPolynomial σ ℤ) (f : σ → Polynomial ℂ) (d : σ → ℕ)
    (hf : ∀ v, (f v).natDegree ≤ d v) (δ : ℕ)
    (hP : ∀ m ∈ P.support, ∑ v ∈ m.support, m v * d v ≤ δ) :
    (eval₂ (Int.castRingHom (Polynomial ℂ)) f P).natDegree ≤ δ := by
  rw [eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [eq_intCast, ← Polynomial.C_eq_intCast]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ((sum_le_sum fun v _ => ?_).trans (hP m hm))
  refine Polynomial.natDegree_pow_le.trans ?_
  exact Nat.mul_le_mul_left _ (hf v)

/-! ### The numeric forms -/

/-- the forms `x_j^{k-1} - f_j^a(x)` -/
noncomputable def F (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (j : Fin n) :
    MvPolynomial (Fin n) ℂ :=
  X j ^ (k - 1) - ∑ t : Fin (k - 1) → Fin n, C (a (j, t)) * ∏ s, X (t s)

/-- the linear-times-power part `x_i^{k-2} (u · x)` -/
noncomputable def ψ0 (i : Fin n) (u : Fin n → ℂ) : MvPolynomial (Fin n) ℂ :=
  X i ^ (k - 1 - 1) * ∑ l, C (u l) * X l

lemma F_hom (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (j : Fin n) :
    (F (k := k) a j).IsHomogeneous (k - 1) := by
  unfold F
  refine (isHomogeneous_X_pow _ _).sub (IsHomogeneous.sum _ _ _ fun t _ => ?_)
  have h := IsHomogeneous.prod (univ : Finset (Fin (k - 1))) (fun s => (X (t s) :
    MvPolynomial (Fin n) ℂ)) (fun _ => 1) fun s _ => isHomogeneous_X _ _
  have := (isHomogeneous_C (Fin n) (a (j, t))).mul h
  simpa using this

lemma ψ0_hom (hk : 2 ≤ k) (i : Fin n) (u : Fin n → ℂ) :
    (ψ0 (k := k) i u).IsHomogeneous (k - 1) := by
  unfold ψ0
  have h1 : (∑ l, C (u l) * X l : MvPolynomial (Fin n) ℂ).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun l _ => by
      simpa using (isHomogeneous_C (Fin n) (u l)).mul (isHomogeneous_X ℂ l)
  have := (isHomogeneous_X_pow (R := ℂ) i (k - 1 - 1)).mul h1
  rwa [show k - 1 - 1 + 1 = k - 1 by omega] at this

lemma ψ_hom (hk : 2 ≤ k) (i : Fin n) (u : Fin n → ℂ) (y : ℂ) :
    (ψ0 (k := k) i u - C y * X i ^ (k - 1)).IsHomogeneous (k - 1) :=
  (ψ0_hom hk i u).sub (by simpa using (isHomogeneous_C (Fin n) y).mul (isHomogeneous_X_pow i (k - 1)))

lemma eval_ψ (i : Fin n) (u : Fin n → ℂ) (y : ℂ) (p : Fin n → ℂ) (hp : p i = 1) :
    eval p (ψ0 (k := k) i u - C y * X i ^ (k - 1)) = ∑ l, u l * p l - y := by
  simp [ψ0, hp]

/-- homogeneous polynomials scale -/
lemma eval_smul_hom {φ : MvPolynomial (Fin n) ℂ} {d : ℕ} (hφ : φ.IsHomogeneous d) (c : ℂ)
    (x : Fin n → ℂ) : eval (c • x) φ = c ^ d * eval x φ := by
  classical
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, mul_sum]
  refine sum_congr rfl fun μ hμ => ?_
  have hw := hφ (mem_support_iff.mp hμ)
  rw [eval_monomial, eval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, prod_mul_distrib]
  rw [prod_pow_eq_pow_sum]
  have : ∑ v ∈ μ.support, μ v = d := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    exact sum_congr rfl fun v _ => by simp
  rw [this]; ring

/-! ### The generic objects -/

/-- the generic coefficient ring -/
abbrev Rg (n k : ℕ) := MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℂ

/-- the generic forms -/
noncomputable def FG (j : Fin n) : MvPolynomial (Fin n) (Rg n k) :=
  X j ^ (k - 1) - ∑ t : Fin (k - 1) → Fin n, C (X (j, t)) * ∏ s, X (t s)

lemma map_FG (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (j : Fin n) :
    MvPolynomial.map (MvPolynomial.eval a) (FG (k := k) j) = F a j := by
  simp [FG, F, map_sub, map_sum, map_mul, map_prod]

/-- the generic version of `Res(x_i^{k-1}, F_j)` -/
noncomputable def cG (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (i : Fin n) : Rg n k :=
  resF res (Function.update (FG (k := k)) i (X i ^ (k - 1)))

lemma eval_cG (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (i : Fin n)
    (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) :
    MvPolynomial.eval a (cG res i) =
      resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))) := by
  unfold cG
  rw [resF_map, map_update]
  congr 2
  · funext j; exact map_FG a j
  · simp

/-- the generic system with row `i` replaced by `x_i^{k-2}(u·x) - y x_i^{k-1}` -/
noncomputable def YG (i : Fin n) (u : Fin n → ℂ) : Fin n → MvPolynomial (Fin n) (Polynomial (Rg n k)) :=
  Function.update (fun j => MvPolynomial.map Polynomial.C (FG (k := k) j)) i
    (MvPolynomial.map (Polynomial.C.comp C) (ψ0 (k := k) i u) -
      C Polynomial.X * MvPolynomial.map (Polynomial.C.comp C) (X i ^ (k - 1)))

/-- the generic polynomial `q(y)` -/
noncomputable def QG (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (i : Fin n)
    (u : Fin n → ℂ) : Polynomial (Rg n k) :=
  resF res (YG (k := k) i u)

/-- `q` at the numeric tensor `a`, as a resultant with coefficients in `ℂ[y]` -/
lemma QG_map (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (i : Fin n) (u : Fin n → ℂ)
    (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) :
    (QG (k := k) res i u).map (MvPolynomial.eval a) =
      resF res (Function.update (fun j => MvPolynomial.map Polynomial.C (F (k := k) a j)) i
        (MvPolynomial.map Polynomial.C (ψ0 (k := k) i u) -
          C Polynomial.X * MvPolynomial.map Polynomial.C (X i ^ (k - 1)))) := by
  unfold QG YG
  rw [← Polynomial.coe_mapRingHom, resF_map, map_update]
  congr 2
  · funext j
    rw [MvPolynomial.map_map, ← map_FG a j, MvPolynomial.map_map]
    congr 1
    ext <;> simp
  · rw [map_sub, map_mul, MvPolynomial.map_map, MvPolynomial.map_map, map_C]
    congr 2
    · congr 1; ext <;> simp
    · simp
    · congr 1; ext <;> simp

lemma QG_eval (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (i : Fin n) (u : Fin n → ℂ)
    (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (y : ℂ) :
    ((QG (k := k) res i u).map (MvPolynomial.eval a)).eval y =
      resF res (Function.update (F (k := k) a) i (ψ0 (k := k) i u - C y * X i ^ (k - 1))) := by
  rw [QG_map, ← Polynomial.coe_evalRingHom, resF_map, map_update]
  congr 2
  · funext j
    rw [MvPolynomial.map_map]
    have e : (Polynomial.evalRingHom y).comp (Polynomial.C : ℂ →+* Polynomial ℂ) = RingHom.id ℂ := by
      ext; simp
    rw [e, MvPolynomial.map_id]
  · rw [map_sub, map_mul, MvPolynomial.map_map, MvPolynomial.map_map, map_C]
    have e : (Polynomial.evalRingHom y).comp (Polynomial.C : ℂ →+* Polynomial ℂ) = RingHom.id ℂ := by
      ext; simp
    rw [e, MvPolynomial.map_id, MvPolynomial.map_id]
    simp

/-! ### The degree of `q` -/

lemma res_wHom (hk : 2 ≤ k) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (i : Fin n) :
    res.IsWeightedHomogeneous (fun v : ResVar n (fun _ => k - 1) => if v.1 = i then 1 else 0)
      ((k - 1) ^ (n - 1)) := by
  have hD : ∀ j : Fin n, 1 ≤ (fun _ : Fin n => k - 1) j := fun _ => by simp only; omega
  obtain ⟨δ, h⟩ := MvResultant.isWeightedHomogeneous_block res hres i
  have h1 := MvResultant.blockDegree_le hD res hres i δ h
  have h2 := MvResultant.blockDegree_ge hD res hres i δ h
  have hp : ∏ j ∈ Finset.univ.erase i, (fun _ : Fin n => k - 1) j = (k - 1) ^ (n - 1) := by
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  rw [hp] at h1 h2
  rwa [show δ = (k - 1) ^ (n - 1) by omega] at h

lemma natDegree_q_le (hk : 2 ≤ k) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (i : Fin n) (u : Fin n → ℂ)
    (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) :
    ((QG (k := k) res i u).map (MvPolynomial.eval a)).natDegree ≤ (k - 1) ^ (n - 1) := by
  classical
  rw [QG_map, resF_eq_eval₂]
  refine natDegree_eval₂_le res _ (fun v => if v.1 = i then 1 else 0) (fun v => ?_) _ fun m hm => ?_
  · obtain ⟨j, α, hα⟩ := v
    simp only
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, Function.update_self, coeff_sub, coeff_C_mul, coeff_map, coeff_map]
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      refine (Polynomial.natDegree_mul_le).trans ?_
      simp
    · rw [if_neg hj, Function.update_of_ne hj, coeff_map]
      simp
  · have h := res_wHom hk res hres i (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum] at h
    rw [← h]
    exact le_of_eq (sum_congr rfl fun v _ => by simp [smul_eq_mul])

/-! ### From a nonzero certificate to the points -/

lemma points_of_ne (hk : 2 ≤ k) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (i : Fin n) (u : Fin n → ℂ)
    (a : Fin n × (Fin (k - 1) → Fin n) → ℂ)
    (hc : resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))) ≠ 0)
    (hR : Polynomial.resultant ((QG (k := k) res i u).map (MvPolynomial.eval a))
      (Polynomial.derivative ((QG (k := k) res i u).map (MvPolynomial.eval a)))
      ((k - 1) ^ (n - 1)) ((k - 1) ^ (n - 1) - 1) ≠ 0) :
    ∃ P : Finset (Fin n → ℂ), P.card = (k - 1) ^ (n - 1) ∧
      ∀ p ∈ P, p i = 1 ∧ ∀ j, j ≠ i → MvPolynomial.eval p (F (k := k) a j) = 0 := by
  classical
  set δ := (k - 1) ^ (n - 1) with hδ
  have hδ1 : 1 ≤ δ := Nat.one_le_pow _ _ (by omega)
  set q := (QG (k := k) res i u).map (MvPolynomial.eval a) with hq
  have hle := natDegree_q_le hk res hres i u a
  -- the degree is exactly `δ`
  have hdeg : q.natDegree = δ := by
    by_contra hne
    have hlt : q.natDegree < δ := lt_of_le_of_ne hle hne
    apply hR
    by_cases h0 : q.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at h0
      obtain ⟨x, hx⟩ := h0
      rw [← hx, Polynomial.derivative_C, Polynomial.resultant_zero_right, zero_pow (by omega),
        zero_mul]
    · exact Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _ hlt
        ((Polynomial.natDegree_derivative_le q).trans_lt (by omega))
  have hq0 : q ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
  rw [← hdeg, ← Polynomial.natDegree_derivative] at hR
  have hcop : IsCoprime q (Polynomial.derivative q) := by
    by_contra hnc
    exact hR (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hq0, hnc⟩)
  have hsep : q.Separable := (Polynomial.separable_def q).mpr hcop
  set Y := q.roots.toFinset with hY
  have hYcard : Y.card = δ := by
    rw [hY, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hdeg]
  -- each root gives a normalized common zero
  have hpt : ∀ y ∈ Y, ∃ p : Fin n → ℂ, p i = 1 ∧ (∀ j, j ≠ i → eval p (F (k := k) a j) = 0) ∧
      ∑ l, u l * p l = y := by
    intro y hy
    rw [hY, Multiset.mem_toFinset, Polynomial.mem_roots hq0, Polynomial.IsRoot.def,
      hq, QG_eval] at hy
    have hhom : ∀ j, (Function.update (F (k := k) a) i (ψ0 (k := k) i u - C y * X i ^ (k - 1)) j).IsHomogeneous
        ((fun _ : Fin n => k - 1) j) := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact ψ_hom hk j u y
      · rw [Function.update_of_ne hj]; exact F_hom a j
    obtain ⟨x, hx0, hx⟩ := (hres.1 _ hhom).mpr hy
    have hxi : x i ≠ 0 := by
      intro hxi
      apply hc
      have hhom' : ∀ j, (Function.update (F (k := k) a) i (X i ^ (k - 1)) j).IsHomogeneous
          ((fun _ : Fin n => k - 1) j) := by
        intro j
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact isHomogeneous_X_pow _ _
        · rw [Function.update_of_ne hj]; exact F_hom a j
      refine (hres.1 _ hhom').mp ⟨x, hx0, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; simp [hxi]; omega
      · have := hx j; rwa [Function.update_of_ne hj] at this ⊢
    refine ⟨(x i)⁻¹ • x, by simp [hxi], fun j hj => ?_, ?_⟩
    · have := hx j
      rw [Function.update_of_ne hj] at this
      rw [eval_smul_hom (F_hom a j), this, mul_zero]
    · have h1 := hx i
      rw [Function.update_self] at h1
      have h2 := eval_smul_hom (ψ_hom hk i u y) (x i)⁻¹ x
      rw [h1, mul_zero, eval_ψ i u y _ (by simp [hxi])] at h2
      exact sub_eq_zero.mp h2
  choose! pt hpt1 hpt2 hpt3 using hpt
  refine ⟨Y.image pt, ?_, fun p hp => ?_⟩
  · rw [card_image_of_injOn, hYcard]
    intro y1 hy1 y2 hy2 he
    rw [← hpt3 y1 hy1, ← hpt3 y2 hy2, he]
  · obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
    exact ⟨hpt1 y hy, hpt2 y hy⟩

/-! ### The grid system -/

/-- weights of the linear factors `x_j - s x_i` -/
def gw (i j : Fin n) (s : Fin (k - 1)) (l : Fin n) : ℂ :=
  if l = j then 1 else if l = i then -((s : ℕ) : ℂ) else 0

/-- the grid tensor: rows `j ≠ i` give `∏_s (x_j - s x_i)` -/
noncomputable def aStar (i : Fin n) : Fin n × (Fin (k - 1) → Fin n) → ℂ := fun v =>
  if v.1 = i then 0 else
    (if v.2 = fun _ => v.1 then 1 else 0) - ∏ s, gw (k := k) i v.1 s (v.2 s)

lemma F_aStar (i j : Fin n) (hj : j ≠ i) :
    F (k := k) (aStar i) j = ∏ s : Fin (k - 1), (X j - C ((s : ℕ) : ℂ) * X i) := by
  classical
  unfold F aStar
  simp only [if_neg hj, map_sub, sub_mul, sum_sub_distrib]
  have h1 : ∑ t : Fin (k - 1) → Fin n, C (if t = (fun _ => j) then (1 : ℂ) else 0) *
      ∏ s, (X (t s) : MvPolynomial (Fin n) ℂ) = X j ^ (k - 1) := by
    simp only [apply_ite C, map_one, map_zero, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
      if_true, prod_const, card_univ, Fintype.card_fin]
  have h2 : ∑ t : Fin (k - 1) → Fin n, C (∏ s, gw (k := k) i j s (t s)) *
      ∏ s, (X (t s) : MvPolynomial (Fin n) ℂ) =
      ∏ s : Fin (k - 1), (X j - C ((s : ℕ) : ℂ) * X i) := by
    have e : ∀ s : Fin (k - 1), (X j - C ((s : ℕ) : ℂ) * X i : MvPolynomial (Fin n) ℂ) =
        ∑ l, C (gw (k := k) i j s l) * X l := by
      intro s
      have hl : ∀ l, C (gw (k := k) i j s l) * (X l : MvPolynomial (Fin n) ℂ) =
          (if l = j then X j else 0) + (if l = i then -(C ((s : ℕ) : ℂ) * X i) else 0) := by
        intro l
        unfold gw
        by_cases h1 : l = j
        · subst h1; simp [hj]
        · by_cases h2 : l = i
          · subst h2; simp [h1]
          · simp [h1, h2]
      simp only [hl, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
      ring
    simp only [e]
    rw [Fintype.prod_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [map_prod, ← prod_mul_distrib]
  rw [h1, h2]; ring

/-- the grid points -/
noncomputable def gridPt (i : Fin n) (d : {j : Fin n // j ≠ i} → Fin (k - 1)) : Fin n → ℂ :=
  fun j => if h : j = i then 1 else ((d ⟨j, h⟩ : ℕ) : ℂ)

lemma gridPt_inj (i : Fin n) : Function.Injective (gridPt (k := k) i) := by
  intro d1 d2 h
  funext ⟨j, hj⟩
  have := congrFun h j
  simp only [gridPt, dif_neg hj] at this
  exact Fin.ext (by exact_mod_cast this)

lemma grid_card (i : Fin n) :
    (univ.image (gridPt (k := k) i)).card = (k - 1) ^ (n - 1) := by
  rw [card_image_of_injective _ (gridPt_inj i), card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]

lemma grid_zero (i : Fin n) (d : {j : Fin n // j ≠ i} → Fin (k - 1)) (j : Fin n) (hj : j ≠ i) :
    eval (gridPt i d) (F (k := k) (aStar i) j) = 0 := by
  rw [F_aStar i j hj, eval_prod]
  refine prod_eq_zero (mem_univ (d ⟨j, hj⟩)) ?_
  simp [gridPt, hj]

/-- a linear form separating finitely many distinct points -/
lemma exists_separating (P : Finset (Fin n → ℂ)) :
    ∃ u : Fin n → ℂ, Set.InjOn (fun p : Fin n → ℂ => ∑ l, u l * p l) P := by
  classical
  set L : MvPolynomial (Fin n) ℂ :=
    ∏ pq ∈ P.offDiag, ∑ l, C (pq.1 l - pq.2 l) * X l with hL
  have hL0 : L ≠ 0 := by
    rw [hL, prod_ne_zero_iff]
    intro pq hpq h0
    obtain ⟨_, _, hne⟩ := mem_offDiag.mp hpq
    apply hne
    funext l
    have := congrArg (coeff (Finsupp.single l 1)) h0
    rw [coeff_sum, coeff_zero] at this
    simp only [coeff_C_mul, coeff_X', mul_ite, mul_one, mul_zero,
      Finsupp.single_left_inj one_ne_zero, sum_ite_eq', mem_univ, if_true] at this
    exact sub_eq_zero.mp this
  obtain ⟨u, hu⟩ : ∃ u, eval u L ≠ 0 := by
    by_contra h
    push_neg at h
    exact hL0 (MvPolynomial.funext fun x => by simp [h x])
  refine ⟨u, fun p hp q hq he => ?_⟩
  by_contra hne
  apply hu
  rw [hL, eval_prod]
  refine prod_eq_zero (i := (p, q)) (mem_offDiag.mpr ⟨hp, hq, hne⟩) ?_
  simp only [map_sum, eval_mul, eval_C, eval_X]
  have : ∑ l, (p l - q l) * u l = ∑ l, u l * p l - ∑ l, u l * q l := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun l _ => by ring
  rw [this]
  exact sub_eq_zero.mpr he

end GenPtsAux

open GenPtsAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (i : Fin n) :
    ∃ Δ : MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℂ, Δ ≠ 0 ∧
      ∀ a : Fin n × (Fin (k - 1) → Fin n) → ℂ, MvPolynomial.eval a Δ ≠ 0 →
        (∃ P : Finset (Fin n → ℂ), P.card = (k - 1) ^ (n - 1) ∧
          ∀ p ∈ P, p i = 1 ∧ ∀ j, j ≠ i →
            MvPolynomial.eval p (MvPolynomial.X j ^ (k - 1) -
              ∑ t : Fin (k - 1) → Fin n,
                MvPolynomial.C (a (j, t)) * ∏ s, MvPolynomial.X (t s)) = 0) ∧
        MvPolynomial.aeval (fun v : ResVar n (fun _ => k - 1) =>
            MvPolynomial.coeff v.2.1 (Function.update
              (fun j => MvPolynomial.X j ^ (k - 1) -
                ∑ t : Fin (k - 1) → Fin n,
                  MvPolynomial.C (a (j, t)) * ∏ s, MvPolynomial.X (t s))
              i (MvPolynomial.X i ^ (k - 1)) v.1))
          (MvPolynomial.map (Int.castRingHom ℂ) res) ≠ 0 := by
  classical
  set δ := (k - 1) ^ (n - 1) with hδ
  have hδ1 : 1 ≤ δ := Nat.one_le_pow _ _ (by omega)
  -- the grid and a separating linear form
  set Pstar := univ.image (gridPt (k := k) i) with hPstar
  obtain ⟨u, hu⟩ := exists_separating Pstar
  set Δ : Rg n k := cG res i * Polynomial.resultant (QG (k := k) res i u)
    (Polynomial.derivative (QG (k := k) res i u)) δ (δ - 1) with hΔ
  have heval : ∀ a, MvPolynomial.eval a Δ = resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))) *
      Polynomial.resultant ((QG (k := k) res i u).map (MvPolynomial.eval a))
        (Polynomial.derivative ((QG (k := k) res i u).map (MvPolynomial.eval a))) δ (δ - 1) := by
    intro a
    rw [hΔ, eval_mul, eval_cG, Polynomial.derivative_map, Polynomial.resultant_map_map]
  refine ⟨Δ, ?_, fun a ha => ?_⟩
  · -- the certificate is nonzero at the grid tensor
    intro hΔ0
    set a := aStar (k := k) i with ha
    have hcs : resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))) ≠ 0 := by
      intro h0
      have hhom' : ∀ j, (Function.update (F (k := k) a) i (X i ^ (k - 1)) j).IsHomogeneous
          ((fun _ : Fin n => k - 1) j) := by
        intro j
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact isHomogeneous_X_pow _ _
        · rw [Function.update_of_ne hj]; exact F_hom a j
      obtain ⟨x, hx0, hx⟩ := (hres.1 _ hhom').mpr h0
      have hxi : x i = 0 := by
        have := hx i
        rw [Function.update_self] at this
        simp at this
        exact this.1
      apply hx0
      funext j
      by_cases hj : j = i
      · rw [hj, hxi]; rfl
      · have := hx j
        rw [Function.update_of_ne hj, ha, F_aStar i j hj, eval_prod] at this
        simp only [eval_sub, eval_X, eval_mul, eval_C, hxi, mul_zero, sub_zero, prod_const,
          card_univ, Fintype.card_fin] at this
        exact pow_eq_zero_iff (by omega) |>.mp this
    set c := resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))) with hc
    set q := (QG (k := k) res i u).map (MvPolynomial.eval a) with hq
    -- Poisson's formula at the grid
    have hD : ∀ j : Fin n, 1 ≤ (fun _ : Fin n => k - 1) j := fun _ => by simp only; omega
    have hcard' : Pstar.card = ∏ j ∈ univ.erase i, (fun _ : Fin n => k - 1) j := by
      rw [prod_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, hPstar,
        grid_card]
    have hP : ∀ p ∈ Pstar, p i = 1 ∧ ∀ j, j ≠ i → eval p (F (k := k) a j) = 0 := by
      intro p hp
      obtain ⟨d, _, rfl⟩ := mem_image.mp hp
      exact ⟨by simp [gridPt], fun j hj => grid_zero i d j hj⟩
    have hqform : q = Polynomial.C c * ∏ p ∈ Pstar,
        (Polynomial.C (∑ l, u l * p l) - Polynomial.X) := by
      refine Polynomial.funext fun y => ?_
      rw [hq, QG_eval]
      have h := MvResultant.poisson_block hD res hres i (F (k := k) a) (fun j _ => F_hom a j)
        Pstar hcard' hP (ψ0 (k := k) i u - C y * X i ^ (k - 1)) (ψ_hom hk i u y)
      have h' : resF res (Function.update (F (k := k) a) i (ψ0 (k := k) i u - C y * X i ^ (k - 1))) =
          c * ∏ p ∈ Pstar, eval p (ψ0 (k := k) i u - C y * X i ^ (k - 1)) := h
      rw [h', Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      congr 1
      refine prod_congr rfl fun p hp => ?_
      rw [eval_ψ (k := k) i u y p (hP p hp).1]
      simp [Polynomial.eval_finset_sum]
    have hneg : ∏ p ∈ Pstar, (Polynomial.C (∑ l, u l * p l) - Polynomial.X) =
        Polynomial.C ((-1 : ℂ) ^ Pstar.card) *
          ∏ p ∈ Pstar, (Polynomial.X - Polynomial.C (∑ l, u l * p l)) := by
      rw [map_pow, map_neg, map_one, ← prod_const, ← prod_mul_distrib]
      exact prod_congr rfl fun p _ => by ring
    rw [hneg, ← mul_assoc, ← map_mul] at hqform
    set c' := c * (-1) ^ Pstar.card with hc'
    have hc'0 : c' ≠ 0 := mul_ne_zero hcs (pow_ne_zero _ (by norm_num))
    have hsep0 : (∏ p ∈ Pstar, (Polynomial.X - Polynomial.C (∑ l, u l * p l))).Separable :=
      Polynomial.separable_prod_X_sub_C_iff'.mpr hu
    have hunit : IsUnit (Polynomial.C c') := Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hc'0)
    have hcop : IsCoprime q (Polynomial.derivative q) := by
      rw [hqform, Polynomial.derivative_C_mul, isCoprime_mul_unit_left_left hunit,
        isCoprime_mul_unit_left_right hunit]
      exact (Polynomial.separable_def _).mp hsep0
    have hdeg : q.natDegree = δ := by
      rw [hqform, Polynomial.natDegree_C_mul hc'0,
        Polynomial.natDegree_finset_prod_X_sub_C_eq_card, hPstar, grid_card]
    have hdeg' : (Polynomial.derivative q).natDegree = δ - 1 := by
      rw [Polynomial.natDegree_derivative, hdeg]
    have hR := Polynomial.resultant_ne_zero q (Polynomial.derivative q) hcop
    rw [hdeg, hdeg'] at hR
    have := heval a
    rw [hΔ0, map_zero] at this
    exact mul_ne_zero hcs hR this.symm
  · rw [heval] at ha
    have hc0 : resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))) ≠ 0 :=
      left_ne_zero_of_mul ha
    have hR := right_ne_zero_of_mul ha
    exact ⟨points_of_ne hk res hres i u a hc0 hR, hc0⟩
