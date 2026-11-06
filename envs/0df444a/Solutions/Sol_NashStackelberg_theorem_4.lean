-- Prove2me | solution 1 for NashStackelberg.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T07:05:58.312481+00:00
-- url     : https://prove2.me/submissions/6cd17c24-11ac-453e-a934-e928165f30e6

import Mathlib
import Definitions.Def_NashStackelberg_IsPNE
import Definitions.Def_NashStackelberg_IsMNE
import Definitions.Def_NashStackelberg_NASP_F
import Definitions.Def_NashStackelberg_NASP_rows
import Definitions.Def_NashStackelberg_NASP_Ftilde
import Definitions.Def_NashStackelberg_NASP_cost
import Definitions.Def_NashStackelberg_Lottery_measure
import Definitions.Def_NashStackelberg_Alg1Output

set_option autoImplicit false

open Matrix

namespace NashStackelberg

lemma exists_between_finset (L U : Finset ℝ) (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : ℝ, (∀ l ∈ L, l ≤ t) ∧ ∀ u ∈ U, t ≤ u := by
  by_cases hL : L.Nonempty
  · exact ⟨L.max' hL, fun l hl => L.le_max' l hl,
      fun u hu => L.max'_le hL u (fun l hl => h l hl u hu)⟩
  · by_cases hU : U.Nonempty
    · exact ⟨U.min' hU, fun l hl => absurd ⟨l, hl⟩ hL, fun u hu => U.min'_le u hu⟩
    · exact ⟨0, fun l hl => absurd ⟨l, hl⟩ hL, fun u hu => absurd ⟨u, hu⟩ hU⟩

lemma poly_reindex {ι R : Type*} [Fintype ι] [Fintype R] (M : Matrix R ι ℝ) (c : R → ℝ) :
    ∃ (r : ℕ) (A : Matrix (Fin r) ι ℝ) (b : Fin r → ℝ),
      {x : ι → ℝ | M *ᵥ x ≤ c} = {x | A *ᵥ x ≤ b} := by
  let e := Fintype.equivFin R
  refine ⟨Fintype.card R, fun k => M (e.symm k), fun k => c (e.symm k), Set.ext fun x => ?_⟩
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h k
    exact h (e.symm k)
  · intro h q
    have h' : (M *ᵥ x) (e.symm (e q)) ≤ c (e.symm (e q)) := h (e q)
    simpa using h'

/-- One Fourier–Motzkin elimination step. -/
lemma fm_step {ι R : Type*} [Fintype ι] [Fintype R] [DecidableEq R] (A : Matrix R ι ℝ)
    (a b : R → ℝ) :
    ∃ (A2 : Matrix (R × R) ι ℝ) (b2 : R × R → ℝ),
      {x : ι → ℝ | ∃ t : ℝ, ∀ k, (A *ᵥ x) k + a k * t ≤ b k} = {x | A2 *ᵥ x ≤ b2} := by
  classical
  let α : R → R → ℝ := fun i j =>
    if 0 < a i ∧ a j < 0 then -a j else if a i = 0 ∧ i = j then 1 else 0
  let β : R → R → ℝ := fun i j => if 0 < a i ∧ a j < 0 then a i else 0
  have hα : ∀ i j, 0 ≤ α i j := by
    intro i j
    simp only [α]
    split_ifs with h1 h2
    · linarith [h1.2]
    · norm_num
    · norm_num
  have hβ : ∀ i j, 0 ≤ β i j := by
    intro i j
    simp only [β]
    split_ifs with h1
    · linarith [h1.1]
    · norm_num
  have hk : ∀ i j, α i j * a i + β i j * a j = 0 := by
    intro i j
    simp only [α, β]
    split_ifs with h1 h2
    · ring
    · rw [h2.1]; ring
    · ring
  let A2 : Matrix (R × R) ι ℝ := fun q l => α q.1 q.2 * A q.1 l + β q.1 q.2 * A q.2 l
  let b2 : R × R → ℝ := fun q => α q.1 q.2 * b q.1 + β q.1 q.2 * b q.2
  have hmul : ∀ (x : ι → ℝ) (i j : R),
      (A2 *ᵥ x) (i, j) = α i j * (A *ᵥ x) i + β i j * (A *ᵥ x) j := by
    intro x i j
    simp only [A2, mulVec, dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  refine ⟨A2, b2, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht⟩ ⟨i, j⟩
    show (A2 *ᵥ x) (i, j) ≤ b2 (i, j)
    rw [hmul]
    have h1 := mul_le_mul_of_nonneg_left (ht i) (hα i j)
    have h2 := mul_le_mul_of_nonneg_left (ht j) (hβ i j)
    have h3 : α i j * (a i * t) + β i j * (a j * t) = 0 := by
      rw [← mul_assoc, ← mul_assoc, ← add_mul, hk, zero_mul]
    simp only [b2]
    rw [mul_add] at h1 h2
    linarith
  · intro hx
    have hrow : ∀ i j, α i j * (A *ᵥ x) i + β i j * (A *ᵥ x) j ≤ α i j * b i + β i j * b j :=
      fun i j => by rw [← hmul]; exact hx (i, j)
    let s : R → ℝ := fun k => b k - (A *ᵥ x) k
    let L : Finset ℝ := (Finset.univ.filter (fun j => a j < 0)).image (fun j => s j / a j)
    let U : Finset ℝ := (Finset.univ.filter (fun i => 0 < a i)).image (fun i => s i / a i)
    obtain ⟨t, htL, htU⟩ := exists_between_finset L U (by
      intro l hl u hu
      simp only [L, U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hl hu
      obtain ⟨j, hj, rfl⟩ := hl
      obtain ⟨i, hi, rfl⟩ := hu
      have hr := hrow i j
      simp only [α, β, if_pos (And.intro hi hj)] at hr
      rw [show s j / a j = (-s j) / (-a j) by rw [neg_div_neg_eq],
        div_le_div_iff₀ (neg_pos.mpr hj) hi]
      simp only [s]
      nlinarith [hr])
    refine ⟨t, fun k => ?_⟩
    rcases lt_trichotomy (a k) 0 with hk0 | hk0 | hk0
    · have h := htL (s k / a k) (Finset.mem_image.mpr ⟨k, by simp [hk0], rfl⟩)
      rw [div_le_iff_of_neg hk0] at h
      simp only [s] at h
      linarith
    · have h := hrow k k
      have hc1 : ¬ (0 < a k ∧ a k < 0) := fun h => by linarith [h.1]
      have h' : (A *ᵥ x) k ≤ b k := by simpa [α, β, hk0] using h
      rw [hk0]
      linarith
    · have h := htU (s k / a k) (Finset.mem_image.mpr ⟨k, by simp [hk0], rfl⟩)
      rw [le_div_iff₀ hk0] at h
      simp only [s] at h
      linarith

/-- Fourier–Motzkin: the projection of a polyhedron is a polyhedron. -/
theorem fm_proj : ∀ (p : ℕ) {ι : Type} [Fintype ι] (r : ℕ) (A : Matrix (Fin r) ι ℝ)
    (B : Matrix (Fin r) (Fin p) ℝ) (b : Fin r → ℝ),
    ∃ (r' : ℕ) (A' : Matrix (Fin r') ι ℝ) (b' : Fin r' → ℝ),
      {x : ι → ℝ | ∃ u, A *ᵥ x + B *ᵥ u ≤ b} = {x | A' *ᵥ x ≤ b'} := by
  intro p
  induction p with
  | zero =>
    intro ι _ r A B b
    have h0 : ∀ u : Fin 0 → ℝ, B *ᵥ u = 0 := fun u => by
      ext k; simp [mulVec, dotProduct]
    refine ⟨r, A, b, Set.ext fun x => ?_⟩
    simp only [Set.mem_setOf_eq, h0, add_zero]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  | succ p ih =>
    intro ι _ r A B b
    classical
    let A1 : Matrix (Fin r) (Option ι) ℝ := fun k o => Option.elim o (B k 0) (A k)
    let B1 : Matrix (Fin r) (Fin p) ℝ := fun k q => B k q.succ
    obtain ⟨r', A', b', hA'⟩ := ih r A1 B1 b
    let A'' : Matrix (Fin r') ι ℝ := fun k l => A' k (some l)
    let a : Fin r' → ℝ := fun k => A' k none
    obtain ⟨A2, b2, h2⟩ := fm_step A'' a b'
    obtain ⟨r3, A3, b3, h3⟩ := poly_reindex A2 b2
    refine ⟨r3, A3, b3, ?_⟩
    rw [← h3, ← h2]
    have e1 : ∀ (t : ℝ) (x : ι → ℝ) (k : Fin r),
        (A1 *ᵥ fun o => Option.elim o t x) k = B k 0 * t + (A *ᵥ x) k := by
      intro t x k
      simp [A1, mulVec, dotProduct, Fintype.sum_option]
    have e2 : ∀ (u : Fin (p + 1) → ℝ) (k : Fin r),
        (B *ᵥ u) k = B k 0 * u 0 + (B1 *ᵥ fun q => u q.succ) k := by
      intro u k
      simp [B1, mulVec, dotProduct, Fin.sum_univ_succ]
    have e3 : ∀ (t : ℝ) (x : ι → ℝ) (k : Fin r'),
        (A' *ᵥ fun o => Option.elim o t x) k = (A'' *ᵥ x) k + a k * t := by
      intro t x k
      simp [A'', a, mulVec, dotProduct, Fintype.sum_option]
      ring
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu⟩
      have hm : (fun o => Option.elim o (u 0) x) ∈ {x' : Option ι → ℝ | ∃ u', A1 *ᵥ x' + B1 *ᵥ u' ≤ b} := by
        refine ⟨fun q => u q.succ, fun k => ?_⟩
        have := hu k
        simp only [Pi.add_apply] at this ⊢
        rw [e1]
        rw [e2] at this
        linarith
      rw [hA'] at hm
      refine ⟨u 0, fun k => ?_⟩
      rw [← e3]
      exact hm k
    · rintro ⟨t, ht⟩
      have hm : (fun o => Option.elim o t x) ∈ {x' : Option ι → ℝ | A' *ᵥ x' ≤ b'} := by
        intro k
        rw [e3]
        exact ht k
      rw [← hA'] at hm
      obtain ⟨u', hu'⟩ := hm
      refine ⟨Fin.cons t u', fun k => ?_⟩
      have := hu' k
      simp only [Pi.add_apply] at this ⊢
      rw [e1] at this
      rw [e2]
      simp only [Fin.cons_zero, Fin.cons_succ]
      linarith

/-! ## Polyhedral algebra -/

def IsPoly {ι : Type} [Fintype ι] (S : Set (ι → ℝ)) : Prop :=
  ∃ (r : ℕ) (A : Matrix (Fin r) ι ℝ) (b : Fin r → ℝ), S = {x | A *ᵥ x ≤ b}

lemma isPoly_of {ι R : Type} [Fintype ι] [Fintype R] (M : Matrix R ι ℝ) (c : R → ℝ) :
    IsPoly {x : ι → ℝ | M *ᵥ x ≤ c} := by
  obtain ⟨r, A, b, h⟩ := poly_reindex M c
  exact ⟨r, A, b, h⟩

lemma IsPoly.inter {ι : Type} [Fintype ι] {S T : Set (ι → ℝ)} (hS : IsPoly S)
    (hT : IsPoly T) : IsPoly (S ∩ T) := by
  obtain ⟨r, A, b, rfl⟩ := hS
  obtain ⟨r', A', b', rfl⟩ := hT
  convert isPoly_of (Matrix.fromRows A A') (Sum.elim b b') using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Matrix.fromRows_mulVec, Sum.elim_le_elim_iff]

lemma isPoly_iInter {ι J : Type} [Fintype ι] [Fintype J] (S : J → Set (ι → ℝ))
    (h : ∀ j, IsPoly (S j)) : IsPoly (⋂ j, S j) := by
  choose r A b hS using h
  convert isPoly_of (Matrix.of fun (p : Σ j, Fin (r j)) => A p.1 p.2) (fun p => b p.1 p.2) using 1
  ext x
  simp only [Set.mem_iInter, hS, Set.mem_setOf_eq, Pi.le_def, Sigma.forall]
  rfl

lemma isPoly_univ {ι : Type} [Fintype ι] : IsPoly (Set.univ : Set (ι → ℝ)) := by
  refine ⟨0, 0, 0, ?_⟩
  ext x
  simp only [Set.mem_univ, Set.mem_setOf_eq, true_iff]
  intro j; exact j.elim0

lemma isPoly_le_lin {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (c : κ → ℝ) : IsPoly {x | L x ≤ c} := by
  convert isPoly_of (LinearMap.toMatrix' L) c using 1
  ext x
  simp only [Set.mem_setOf_eq, LinearMap.toMatrix'_mulVec]

lemma isPoly_eq_lin {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (c : κ → ℝ) : IsPoly {x | L x = c} := by
  convert (isPoly_le_lin L c).inter (isPoly_le_lin (-L) (-c)) using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, LinearMap.neg_apply, neg_le_neg_iff]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

lemma isPoly_le_fun {ι : Type} [Fintype ι] [DecidableEq ι]
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) : IsPoly {x | ℓ x ≤ c} := by
  convert isPoly_le_lin (LinearMap.pi (fun _ : Unit => ℓ)) (fun _ => c) using 1
  ext x
  simp only [Set.mem_setOf_eq, Pi.le_def, LinearMap.pi_apply]
  exact ⟨fun h _ => h, fun h => h ()⟩

lemma isPoly_eq_fun {ι : Type} [Fintype ι] [DecidableEq ι]
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) : IsPoly {x | ℓ x = c} := by
  convert isPoly_eq_lin (LinearMap.pi (fun _ : Unit => ℓ)) (fun _ => c) using 1
  ext x
  simp only [Set.mem_setOf_eq, LinearMap.pi_apply]
  exact ⟨fun h => funext fun _ => h, fun h => congrFun h ()⟩

lemma IsPoly.proj {ι κ : Type} [Fintype ι] [Fintype κ] {S : Set ((ι ⊕ κ) → ℝ)}
    (hS : IsPoly S) : IsPoly {x : ι → ℝ | ∃ u : κ → ℝ, Sum.elim x u ∈ S} := by
  obtain ⟨r, A, b, rfl⟩ := hS
  let e := Fintype.equivFin κ
  obtain ⟨r', A', b', h⟩ := fm_proj (Fintype.card κ) r (A.submatrix id Sum.inl)
    (A.submatrix id (Sum.inr ∘ e.symm)) b
  refine ⟨r', A', b', ?_⟩
  rw [← h]
  have key : ∀ (x : ι → ℝ) (u : κ → ℝ), A *ᵥ Sum.elim x u =
      A.submatrix id Sum.inl *ᵥ x + A.submatrix id (Sum.inr ∘ e.symm) *ᵥ (u ∘ e.symm) := by
    intro x u
    ext j
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.add_apply, Matrix.submatrix_apply, id, Function.comp_apply]
    congr 1
    exact (e.symm.sum_comp (fun k => A j (Sum.inr k) * u k)).symm
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u ∘ e.symm, by rw [← key]; exact hu⟩
  · rintro ⟨u, hu⟩
    refine ⟨u ∘ e, ?_⟩
    rw [key]
    have : (u ∘ e) ∘ e.symm = u := by
      funext t; simp
    rw [this]; exact hu

/-! ## Farkas -/

lemma farkas {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (M : Matrix (Fin m) ι ℝ)
    (g : ι → ℝ) (h : ∀ d : ι → ℝ, M *ᵥ d ≤ 0 → g ⬝ᵥ d ≤ 0) :
    ∃ μ : Fin m → ℝ, 0 ≤ μ ∧ Mᵀ *ᵥ μ = g := by
  let S : Set ((ι ⊕ Fin m) → ℝ) :=
    {z | (-(LinearMap.funLeft ℝ ℝ (Sum.inr : Fin m → ι ⊕ Fin m))) z ≤ 0} ∩
     {z | (Mᵀ.mulVecLin ∘ₗ LinearMap.funLeft ℝ ℝ (Sum.inr : Fin m → ι ⊕ Fin m) -
        LinearMap.funLeft ℝ ℝ (Sum.inl : ι → ι ⊕ Fin m)) z = 0}
  have hS : IsPoly S := (isPoly_le_lin _ _).inter (isPoly_eq_lin _ _)
  obtain ⟨r, A, b, hC⟩ := hS.proj
  have mem : ∀ g', g' ∈ {x : ι → ℝ | ∃ u : Fin m → ℝ, Sum.elim x u ∈ S} ↔
      ∃ μ : Fin m → ℝ, 0 ≤ μ ∧ Mᵀ *ᵥ μ = g' := by
    intro g'
    simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, LinearMap.neg_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
      neg_nonpos, sub_eq_zero]
    have h1 : ∀ u : Fin m → ℝ, (fun j => Sum.elim g' u (Sum.inr j)) = u := fun u => rfl
    have h2 : (fun j => Sum.elim g' (0 : Fin m → ℝ) (Sum.inl j)) = g' := rfl
    constructor
    · rintro ⟨u, hu1, hu2⟩
      exact ⟨u, hu1, hu2⟩
    · rintro ⟨u, hu1, hu2⟩
      exact ⟨u, hu1, hu2⟩
  by_contra hne
  have mem' : ∀ g', (∃ μ : Fin m → ℝ, 0 ≤ μ ∧ Mᵀ *ᵥ μ = g') → A *ᵥ g' ≤ b := by
    intro g' hg'
    have : g' ∈ {x | A *ᵥ x ≤ b} := by rw [← hC]; exact (mem g').2 hg'
    exact this
  have hg : ¬ (A *ᵥ g ≤ b) := fun hgb => hne ((mem g).1 (by rw [hC]; exact hgb))
  simp only [Pi.le_def, not_forall, not_le] at hg
  obtain ⟨k, hk⟩ := hg
  have h0 : 0 ≤ b k := by
    have := mem' 0 ⟨0, le_rfl, by simp⟩
    simpa using this k
  have hrow : ∀ j, (fun i => A k i) ⬝ᵥ (fun i => M j i) ≤ 0 := by
    intro j
    by_contra hpos
    push_neg at hpos
    set a := (fun i => A k i) ⬝ᵥ (fun i => M j i) with ha
    have hnn : 0 ≤ Pi.single (M := fun _ : Fin m => ℝ) j ((b k + 1) / a) := by
      intro t
      by_cases htj : t = j
      · subst htj
        simp only [Pi.single_eq_same, Pi.zero_apply]
        exact div_nonneg (by linarith) hpos.le
      · simp [Pi.single_eq_of_ne htj]
    have heq : Mᵀ *ᵥ Pi.single j ((b k + 1) / a) = ((b k + 1) / a) • (fun i => M j i) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    have hm := mem' (((b k + 1) / a) • (fun i => M j i)) ⟨_, hnn, heq⟩ k
    rw [Matrix.mulVec_smul] at hm
    simp only [Pi.smul_apply, smul_eq_mul] at hm
    have : (A *ᵥ fun i => M j i) k = a := rfl
    rw [this, div_mul_cancel₀ _ hpos.ne'] at hm
    linarith
  have := h (fun i => A k i) (fun j => by
    simpa [Matrix.mulVec, dotProduct_comm] using hrow j)
  have e : g ⬝ᵥ (fun i => A k i) = (A *ᵥ g) k := by
    simp [Matrix.mulVec, dotProduct_comm]
  linarith

/-! ## KKT for a convex QP -/

lemma quad_expand {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (ℓ y w : Fin d → ℝ) :
    (1/2:ℝ) * ((y + w) ⬝ᵥ (Q *ᵥ (y + w))) + ℓ ⬝ᵥ (y + w) =
      (1/2:ℝ) * (y ⬝ᵥ (Q *ᵥ y)) + ℓ ⬝ᵥ y + ((1/2:ℝ) • ((Q + Qᵀ) *ᵥ y) + ℓ) ⬝ᵥ w
        + (1/2:ℝ) * (w ⬝ᵥ (Q *ᵥ w)) := by
  have h1 : (Qᵀ *ᵥ y) ⬝ᵥ w = y ⬝ᵥ (Q *ᵥ w) := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have h2 : (Q *ᵥ y) ⬝ᵥ w = w ⬝ᵥ (Q *ᵥ y) := dotProduct_comm _ _
  simp only [Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add, add_dotProduct,
    smul_dotProduct, smul_eq_mul, h1, h2]
  ring

lemma kkt {d r : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : ∀ v, 0 ≤ v ⬝ᵥ (Q *ᵥ v))
    (ℓ : Fin d → ℝ) (B : Matrix (Fin r) (Fin d) ℝ) (β : Fin r → ℝ) (y : Fin d → ℝ)
    (hy : B *ᵥ y ≤ β) :
    (∀ v, B *ᵥ v ≤ β → (1/2:ℝ) * (y ⬝ᵥ (Q *ᵥ y)) + ℓ ⬝ᵥ y ≤
        (1/2:ℝ) * (v ⬝ᵥ (Q *ᵥ v)) + ℓ ⬝ᵥ v) ↔
    ∃ μ : Fin r → ℝ, 0 ≤ μ ∧ (1/2:ℝ) • ((Q + Qᵀ) *ᵥ y) + ℓ + Bᵀ *ᵥ μ = 0 ∧
      ∀ j, μ j * (β j - (B *ᵥ y) j) = 0 := by
  set G := (1/2:ℝ) • ((Q + Qᵀ) *ᵥ y) + ℓ with hG
  have expand : ∀ v, (1/2:ℝ) * (v ⬝ᵥ (Q *ᵥ v)) + ℓ ⬝ᵥ v =
      (1/2:ℝ) * (y ⬝ᵥ (Q *ᵥ y)) + ℓ ⬝ᵥ y + G ⬝ᵥ (v - y)
        + (1/2:ℝ) * ((v - y) ⬝ᵥ (Q *ᵥ (v - y))) := by
    intro v
    have := quad_expand Q ℓ y (v - y)
    rw [add_sub_cancel] at this
    exact this
  constructor
  · intro hopt
    classical
    let M : Matrix (Fin r) (Fin d) ℝ :=
      Matrix.of fun j i => if (B *ᵥ y) j = β j then B j i else 0
    obtain ⟨μ, hμ0, hμ⟩ := farkas r M (-G) (by
      intro dd hdd
      have hpos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
      have hrows : ∀ j, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
          (B *ᵥ (y + t • dd)) j ≤ β j := by
        intro j
        have e : ∀ t : ℝ, (B *ᵥ (y + t • dd)) j = (B *ᵥ y) j + t * (B *ᵥ dd) j := by
          intro t; simp [Matrix.mulVec_add, Matrix.mulVec_smul]
        by_cases hj : (B *ᵥ y) j = β j
        · have hMj : (B *ᵥ dd) j ≤ 0 := by
            have := hdd j
            have hj' := hj
            simp only [Matrix.mulVec, dotProduct] at hj'
            simpa [M, Matrix.mulVec, dotProduct, hj'] using this
          filter_upwards [hpos] with t ht
          rw [e, hj]; nlinarith
        · have hlt : (B *ᵥ y) j < β j := lt_of_le_of_ne (hy j) hj
          have hc : ContinuousAt (fun t : ℝ => (B *ᵥ y) j + t * (B *ᵥ dd) j) 0 := by fun_prop
          have := hc.eventually_lt continuousAt_const (by simpa using hlt)
          filter_upwards [nhdsWithin_le_nhds this] with t ht
          rw [e]; exact ht.le
      have hev2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
          0 ≤ G ⬝ᵥ dd + t * ((1/2:ℝ) * (dd ⬝ᵥ (Q *ᵥ dd))) := by
        filter_upwards [hpos, Filter.eventually_all.2 hrows] with t ht hf
        have h1 := hopt _ (fun j => hf j)
        rw [expand (y + t • dd)] at h1
        simp only [add_sub_cancel_left, dotProduct_smul, smul_dotProduct, Matrix.mulVec_smul,
          smul_eq_mul] at h1
        have : 0 ≤ t * (G ⬝ᵥ dd + t * ((1/2:ℝ) * (dd ⬝ᵥ (Q *ᵥ dd)))) := by linarith
        exact (mul_nonneg_iff_of_pos_left ht).1 this
      have htend : Filter.Tendsto (fun t : ℝ => G ⬝ᵥ dd + t * ((1/2:ℝ) * (dd ⬝ᵥ (Q *ᵥ dd))))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (G ⬝ᵥ dd)) :=
        ((continuous_const.add (continuous_id.mul continuous_const)).tendsto' 0 _
          (by simp)).mono_left nhdsWithin_le_nhds
      have := ge_of_tendsto htend hev2
      rw [neg_dotProduct]; linarith)
    refine ⟨fun j => if (B *ᵥ y) j = β j then μ j else 0, ?_, ?_, ?_⟩
    · intro j
      by_cases h : (B *ᵥ y) j = β j
      · simp only [h, if_true]; exact hμ0 j
      · simp [h]
    · have : Bᵀ *ᵥ (fun j => if (B *ᵥ y) j = β j then μ j else 0) = Mᵀ *ᵥ μ := by
        ext i
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, M, Matrix.of_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [this, hμ]; simp
    · intro j
      by_cases h : (B *ᵥ y) j = β j <;> simp [h]
  · rintro ⟨μ, hμ0, hst, hcs⟩ v hv
    rw [expand v]
    have hGμ : G = -(Bᵀ *ᵥ μ) := eq_neg_of_add_eq_zero_left hst
    have hq := hQ (v - y)
    have key : 0 ≤ G ⬝ᵥ (v - y) := by
      rw [hGμ, neg_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_sub, dotProduct_sub]
      have h1 : μ ⬝ᵥ (B *ᵥ v) ≤ μ ⬝ᵥ β :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hμ0 j)
      have h2 : μ ⬝ᵥ β = μ ⬝ᵥ (B *ᵥ y) := by
        have : μ ⬝ᵥ (β - B *ᵥ y) = 0 := Finset.sum_eq_zero fun j _ => by simpa using hcs j
        rw [dotProduct_sub] at this; linarith
      linarith
    nlinarith

/-! ## Follower KKT and the pieces of F -/

lemma sol_iff {nl : ℕ} (G : FollowerGame nl) (w : Fin nl → ℝ)
    (y : (k : Fin G.K) → Fin (G.d k) → ℝ) :
    y ∈ G.SOL w ↔ ∀ k, G.A k *ᵥ w + G.B k *ᵥ y k ≤ G.b k ∧
      ∃ μ : Fin (G.r k) → ℝ, 0 ≤ μ ∧
        (1/2:ℝ) • ((G.Q k + (G.Q k)ᵀ) *ᵥ y k) +
          (G.c k + ∑ k' ∈ Finset.univ.erase k, G.C k k' *ᵥ y k' + G.H k *ᵥ w) +
          (G.B k)ᵀ *ᵥ μ = 0 ∧
        ∀ j, μ j * (G.b k j - (G.A k *ᵥ w + G.B k *ᵥ y k) j) = 0 := by
  classical
  simp only [FollowerGame.SOL, IsPNE, Set.mem_setOf_eq]
  refine forall_congr' fun k => ?_
  set ℓ := G.c k + ∑ k' ∈ Finset.univ.erase k, G.C k k' *ᵥ y k' + G.H k *ᵥ w with hℓ
  have hcost : ∀ v, (1/2:ℝ) * (Function.update y k v k ⬝ᵥ (G.Q k *ᵥ Function.update y k v k))
      + G.c k ⬝ᵥ Function.update y k v k
      + (∑ k' ∈ Finset.univ.erase k, G.C k k' *ᵥ Function.update y k v k') ⬝ᵥ
          Function.update y k v k
      + (G.H k *ᵥ w) ⬝ᵥ Function.update y k v k
      = (1/2:ℝ) * (v ⬝ᵥ (G.Q k *ᵥ v)) + ℓ ⬝ᵥ v := by
    intro v
    have hs : ∑ k' ∈ Finset.univ.erase k, G.C k k' *ᵥ Function.update y k v k' =
        ∑ k' ∈ Finset.univ.erase k, G.C k k' *ᵥ y k' :=
      Finset.sum_congr rfl fun k' hk' => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
    rw [hs, Function.update_self]
    simp only [hℓ, add_dotProduct]
    ring
  have hcost0 : (1/2:ℝ) * (y k ⬝ᵥ (G.Q k *ᵥ y k)) + G.c k ⬝ᵥ y k
      + (∑ k' ∈ Finset.univ.erase k, G.C k k' *ᵥ y k') ⬝ᵥ y k + (G.H k *ᵥ w) ⬝ᵥ y k
      = (1/2:ℝ) * (y k ⬝ᵥ (G.Q k *ᵥ y k)) + ℓ ⬝ᵥ y k := by
    have := hcost (y k)
    rwa [Function.update_eq_self] at this
  have hfeas : ∀ v, G.A k *ᵥ w + G.B k *ᵥ v ≤ G.b k ↔ G.B k *ᵥ v ≤ G.b k - G.A k *ᵥ w := by
    intro v
    simp only [Pi.le_def, Pi.add_apply, Pi.sub_apply]
    exact forall_congr' fun j => by constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨hy, hopt⟩
    refine ⟨hy, ?_⟩
    have hy' := (hfeas _).1 hy
    obtain ⟨μ, hμ0, hst, hcs⟩ := (kkt (G.Q k) (G.Q_psd k) ℓ (G.B k) _ (y k) hy').1 (by
      intro v hv
      have := hopt v ((hfeas v).2 hv)
      rw [hcost0, hcost v] at this
      exact this)
    refine ⟨μ, hμ0, hst, fun j => ?_⟩
    have := hcs j
    simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
    rw [← this]; ring
  · rintro ⟨hy, μ, hμ0, hst, hcs⟩
    refine ⟨hy, ?_⟩
    have hy' := (hfeas _).1 hy
    have h := (kkt (G.Q k) (G.Q_psd k) ℓ (G.B k) _ (y k) hy').2 ⟨μ, hμ0, hst, fun j => by
      have := hcs j
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
      rw [← this]; ring⟩
    intro v hv
    have := h v ((hfeas v).1 hv)
    rw [hcost0, hcost v]
    exact this

section Pieces
variable {n : ℕ} (N : NASP n) (i : Fin n)

abbrev Kap := Σ k : Fin (N.P i).K, Fin ((N.P i).r k)

def slackv (z : (N.Var i ⊕ Kap N i) → ℝ) (k : Fin (N.P i).K) : Fin ((N.P i).r k) → ℝ :=
  (N.P i).A k *ᵥ (fun a => z (.inl (.inl a))) + (N.P i).B k *ᵥ (fun l => z (.inl (.inr ⟨k, l⟩)))

noncomputable def statv (z : (N.Var i ⊕ Kap N i) → ℝ) (k : Fin (N.P i).K) : Fin ((N.P i).d k) → ℝ :=
  (1/2:ℝ) • (((N.P i).Q k + ((N.P i).Q k)ᵀ) *ᵥ (fun l => z (.inl (.inr ⟨k, l⟩)))) +
    ((N.P i).c k + ∑ k' ∈ Finset.univ.erase k,
        (N.P i).C k k' *ᵥ (fun l => z (.inl (.inr ⟨k', l⟩))) +
      (N.P i).H k *ᵥ (fun a => z (.inl (.inl a)))) +
    ((N.P i).B k)ᵀ *ᵥ (fun j => z (.inr ⟨k, j⟩))

def piece (θ : Kap N i → Bool) : Set ((N.Var i ⊕ Kap N i) → ℝ) :=
  {z | N.AS i *ᵥ (fun a => z (.inl a)) ≤ N.bS i} ∩ (⋂ k, {z | slackv N i z k ≤ (N.P i).b k}) ∩
    (⋂ p : Kap N i, {z | 0 ≤ z (.inr p)}) ∩ (⋂ k, {z | statv N i z k = 0}) ∩
    (⋂ p : Kap N i, if θ p then {z | z (.inr p) = 0}
      else {z | slackv N i z p.1 p.2 = (N.P i).b p.1 p.2})

lemma isPoly_piece (θ : Kap N i → Bool) : IsPoly (piece N i θ) := by
  classical
  let X : ((N.Var i ⊕ Kap N i) → ℝ) →ₗ[ℝ] (N.Var i → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inl
  let W : ((N.Var i ⊕ Kap N i) → ℝ) →ₗ[ℝ] (Fin (N.nl i) → ℝ) :=
    LinearMap.pi (fun a => LinearMap.proj (Sum.inl (Sum.inl a)))
  let Y : ∀ k, ((N.Var i ⊕ Kap N i) → ℝ) →ₗ[ℝ] (Fin ((N.P i).d k) → ℝ) := fun k =>
    LinearMap.pi (fun l => LinearMap.proj (Sum.inl (Sum.inr ⟨k, l⟩)))
  let Λ : ∀ k, ((N.Var i ⊕ Kap N i) → ℝ) →ₗ[ℝ] (Fin ((N.P i).r k) → ℝ) := fun k =>
    LinearMap.pi (fun j => LinearMap.proj (Sum.inr ⟨k, j⟩))
  let S : ∀ k, ((N.Var i ⊕ Kap N i) → ℝ) →ₗ[ℝ] (Fin ((N.P i).r k) → ℝ) := fun k =>
    ((N.P i).A k).mulVecLin ∘ₗ W + ((N.P i).B k).mulVecLin ∘ₗ Y k
  have hS : ∀ k z, S k z = slackv N i z k := fun k z => rfl
  let T : ∀ k, ((N.Var i ⊕ Kap N i) → ℝ) →ₗ[ℝ] (Fin ((N.P i).d k) → ℝ) := fun k =>
    (1/2:ℝ) • ((((N.P i).Q k + ((N.P i).Q k)ᵀ)).mulVecLin ∘ₗ Y k) +
      (∑ k' ∈ Finset.univ.erase k, ((N.P i).C k k').mulVecLin ∘ₗ Y k' +
        ((N.P i).H k).mulVecLin ∘ₗ W) + (((N.P i).B k)ᵀ).mulVecLin ∘ₗ Λ k
  have hT : ∀ k z, statv N i z k = T k z + (N.P i).c k := by
    intro k z
    funext l
    simp only [statv, T, Y, W, Λ, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.sum_apply, Matrix.mulVecLin_apply, Pi.add_apply,
      Pi.smul_apply, Finset.sum_apply, Matrix.mulVec, dotProduct, LinearMap.pi_apply,
      LinearMap.proj_apply, smul_eq_mul]
    ring
  refine (((((isPoly_le_lin ((N.AS i).mulVecLin ∘ₗ X) (N.bS i)).inter
    (isPoly_iInter _ fun k => isPoly_le_lin (S k) _)).inter
    (isPoly_iInter _ fun p => ?_)).inter (isPoly_iInter _ fun k => ?_)).inter
    (isPoly_iInter _ fun p => ?_))
  · convert isPoly_le_fun (-(LinearMap.proj (R := ℝ) (φ := fun _ : N.Var i ⊕ Kap N i => ℝ)
      (Sum.inr p))) 0 using 1
    ext z
    simp
  · convert isPoly_eq_lin (T k) (-(N.P i).c k) using 1
    ext z
    simp only [Set.mem_setOf_eq, hT]
    exact ⟨fun h => eq_neg_of_add_eq_zero_left h, fun h => by rw [h]; simp⟩
  · split_ifs
    · exact isPoly_eq_fun (LinearMap.proj (R := ℝ) (φ := fun _ : N.Var i ⊕ Kap N i => ℝ)
        (Sum.inr p)) 0
    · exact isPoly_eq_fun (LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) p.2 ∘ₗ S p.1) _

lemma F_eq_pieces : N.F i = ⋃ θ : Kap N i → Bool,
    {x : N.Var i → ℝ | ∃ μ : Kap N i → ℝ, Sum.elim x μ ∈ piece N i θ} := by
  classical
  ext x
  simp only [NASP.F, Set.mem_setOf_eq, sol_iff, Set.mem_iUnion, piece, Set.mem_inter_iff,
    Set.mem_iInter, slackv, statv, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hAS, h⟩
    choose hfeas μk hμ0 hst hcs using h
    refine ⟨fun p => decide (μk p.1 p.2 = 0), fun p => μk p.1 p.2,
      ⟨⟨⟨⟨hAS, hfeas⟩, fun p => hμ0 p.1 p.2⟩, hst⟩, fun p => ?_⟩⟩
    by_cases h0 : μk p.1 p.2 = 0
    · simp only [h0, decide_true, if_true, Set.mem_setOf_eq, Sum.elim_inr]
    · simp only [h0, decide_false, Bool.false_eq_true, if_false, Set.mem_setOf_eq,
        Sum.elim_inl]
      have := hcs p.1 p.2
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 h0
      · linarith
  · rintro ⟨θ, μ, ⟨⟨⟨hAS, hfeas⟩, hμ0⟩, hst⟩, hθ⟩
    refine ⟨hAS, fun k => ⟨hfeas k, fun j => μ ⟨k, j⟩, fun j => hμ0 ⟨k, j⟩, hst k, fun j => ?_⟩⟩
    have := hθ ⟨k, j⟩
    split_ifs at this with hθk
    · simp only [Set.mem_setOf_eq, Sum.elim_inr] at this
      show μ ⟨k, j⟩ * _ = 0
      rw [this, zero_mul]
    · simp only [Set.mem_setOf_eq, Sum.elim_inl] at this
      show μ ⟨k, j⟩ * _ = 0
      rw [this, sub_self, mul_zero]

theorem part_a1 : ∃ (m : (Fin (N.rows i) → Bool) → ℕ)
    (A : (θ : Fin (N.rows i) → Bool) → Matrix (Fin (m θ)) (N.Var i) ℝ)
    (b : (θ : Fin (N.rows i) → Bool) → Fin (m θ) → ℝ),
    N.F i = ⋃ θ, {x | A θ *ᵥ x ≤ b θ} := by
  let e : Kap N i ≃ Fin (N.rows i) := finSigmaFinEquiv
  choose m A b h using fun θ : Fin (N.rows i) → Bool => (isPoly_piece N i (θ ∘ e)).proj
  refine ⟨m, A, b, ?_⟩
  rw [F_eq_pieces]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨θ, hx⟩
    refine ⟨θ ∘ e.symm, ?_⟩
    rw [← h]
    have : (θ ∘ e.symm) ∘ e = θ := by funext p; simp
    rw [this]; exact hx
  · rintro ⟨θ, hx⟩
    exact ⟨θ ∘ e, by rw [h]; exact hx⟩

end Pieces

end NashStackelberg

open MeasureTheory ProbabilityTheory Matrix

namespace NashStackelberg

section CostAlg

variable {n : ℕ} (N : NASP n)

lemma cost_update (i : Fin n) (x : (j : Fin n) → N.Var j → ℝ) (x' : N.Var i → ℝ) :
    N.cost i (Function.update x i x') =
      (N.c i + ∑ j ∈ Finset.univ.erase i, N.C i j *ᵥ x j) ⬝ᵥ x' := by
  unfold NASP.cost
  rw [add_dotProduct, Function.update_self]
  congr 2
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma cost_update' (i : Fin n) (x : (j : Fin n) → N.Var j → ℝ) (x' : N.Var i → ℝ) :
    N.cost i (Function.update x i x') =
      N.c i ⬝ᵥ x' + ∑ j ∈ Finset.univ.erase i, (x' ᵥ* N.C i j) ⬝ᵥ x j := by
  rw [cost_update, add_dotProduct, sum_dotProduct]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dotProduct_comm, dotProduct_mulVec]

lemma cost_expand (i : Fin n) (x : (j : Fin n) → N.Var j → ℝ) :
    N.cost i x = N.c i ⬝ᵥ x i + ∑ j ∈ Finset.univ.erase i, (N.C i j *ᵥ x j) ⬝ᵥ x i := by
  unfold NASP.cost
  rw [sum_dotProduct]

end CostAlg

section Meas

variable {n : ℕ} {V : Fin n → Type*} [∀ i, Fintype (V i)]
  (σ : (i : Fin n) → Measure (V i → ℝ)) [∀ i, IsProbabilityMeasure (σ i)]

lemma integrable_coord (hσ : ∀ i, Integrable id (σ i)) (j : Fin n) :
    Integrable (fun x : (i : Fin n) → V i → ℝ => x j) (Measure.pi σ) :=
  ((measurePreserving_eval (μ := σ) j).integrable_comp (g := id)
    (hσ j).aestronglyMeasurable).mpr (hσ j)

lemma integral_coord (hσ : ∀ i, Integrable id (σ i)) (j : Fin n) :
    ∫ x, x j ∂(Measure.pi σ) = ∫ y, y ∂(σ j) := by
  have h := measurePreserving_eval (μ := σ) j
  calc ∫ x, x j ∂(Measure.pi σ)
      = ∫ y, y ∂(Measure.map (Function.eval j) (Measure.pi σ)) :=
        (integral_map h.measurable.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ y, y ∂(σ j) := by rw [h.map_eq]

lemma integrable_coord_a (hσ : ∀ i, Integrable id (σ i)) (j : Fin n) (a : V j) :
    Integrable (fun x : (i : Fin n) → V i → ℝ => x j a) (Measure.pi σ) :=
  integrable_pi_iff.mp (integrable_coord σ hσ j) a

lemma integral_coord_a (hσ : ∀ i, Integrable id (σ i)) (j : Fin n) (a : V j) :
    ∫ x, x j a ∂(Measure.pi σ) = (∫ y, y ∂(σ j)) a := by
  rw [← integral_coord σ hσ j, eval_integral (fun a => integrable_coord_a σ hσ j a)]

lemma lin_exp (hσ : ∀ i, Integrable id (σ i)) (j : Fin n) (w : V j → ℝ) :
    Integrable (fun x : (i : Fin n) → V i → ℝ => w ⬝ᵥ x j) (Measure.pi σ) ∧
      ∫ x, w ⬝ᵥ x j ∂(Measure.pi σ) = w ⬝ᵥ (∫ y, y ∂(σ j)) := by
  unfold dotProduct
  refine ⟨integrable_finsetSum _ (fun a _ => (integrable_coord_a σ hσ j a).const_mul (w a)), ?_⟩
  rw [integral_finsetSum _ (fun a _ => (integrable_coord_a σ hσ j a).const_mul (w a))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [integral_const_mul, integral_coord_a σ hσ j a]

lemma indep_coords {i j : Fin n} (hji : j ≠ i) :
    IndepFun (fun x : (k : Fin n) → V k → ℝ => x j) (fun x => x i) (Measure.pi σ) := by
  have h := iIndepFun_pi (μ := σ) (X := fun k (y : V k → ℝ) => y) (fun k => aemeasurable_id)
  exact h.indepFun hji

lemma bilin_exp (hσ : ∀ i, Integrable id (σ i)) {i j : Fin n} (hji : j ≠ i)
    (C : Matrix (V i) (V j) ℝ) :
    Integrable (fun x : (k : Fin n) → V k → ℝ => (C *ᵥ x j) ⬝ᵥ x i) (Measure.pi σ) ∧
      ∫ x, (C *ᵥ x j) ⬝ᵥ x i ∂(Measure.pi σ) =
        (C *ᵥ (∫ y, y ∂(σ j))) ⬝ᵥ (∫ y, y ∂(σ i)) := by
  have hind : ∀ a : V i, IndepFun (fun x : (k : Fin n) → V k → ℝ => (fun b => C a b) ⬝ᵥ x j)
      (fun x => x i a) (Measure.pi σ) := by
    intro a
    have hm1 : Measurable (fun v : V j → ℝ => (fun b => C a b) ⬝ᵥ v) := by
      show Measurable (fun v : V j → ℝ => ∑ b, C a b * v b)
      exact Finset.measurable_sum _ (fun b _ => by fun_prop)
    have hm2 : Measurable (fun v : V i → ℝ => v a) := measurable_pi_apply a
    exact (indep_coords σ hji).comp hm1 hm2
  have hint : ∀ a : V i, Integrable
      (fun x : (k : Fin n) → V k → ℝ => (fun b => C a b) ⬝ᵥ x j * x i a) (Measure.pi σ) :=
    fun a => (hind a).integrable_mul (lin_exp σ hσ j _).1 (integrable_coord_a σ hσ i a)
  have hrw : (fun x : (k : Fin n) → V k → ℝ => (C *ᵥ x j) ⬝ᵥ x i) =
      fun x => ∑ a, (fun b => C a b) ⬝ᵥ x j * x i a := by
    funext x; rfl
  rw [hrw]
  refine ⟨integrable_finsetSum _ (fun a _ => hint a), ?_⟩
  rw [integral_finsetSum _ (fun a _ => hint a)]
  show _ = ∑ a, (C *ᵥ (∫ y, y ∂(σ j))) a * (∫ y, y ∂(σ i)) a
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [(hind a).integral_fun_mul_eq_mul_integral (lin_exp σ hσ j _).1.aestronglyMeasurable
    (integrable_coord_a σ hσ i a).aestronglyMeasurable, (lin_exp σ hσ j _).2,
    integral_coord_a σ hσ i a]
  rfl

end Meas

section CostExp

variable {n : ℕ} (N : NASP n) (σ : (i : Fin n) → Measure (N.Var i → ℝ))
  [∀ i, IsProbabilityMeasure (σ i)]

lemma cost_exp (hσ : ∀ i, Integrable id (σ i)) (i : Fin n) :
    Integrable (N.cost i) (Measure.pi σ) ∧
      ∫ x, N.cost i x ∂(Measure.pi σ) = N.cost i (fun j => ∫ y, y ∂(σ j)) := by
  have he : N.cost i = fun x => N.c i ⬝ᵥ x i +
      ∑ j ∈ Finset.univ.erase i, (N.C i j *ᵥ x j) ⬝ᵥ x i := by
    funext x; exact cost_expand N i x
  rw [he]
  beta_reduce
  have h1 := lin_exp σ hσ i (N.c i)
  have h2 : ∀ j ∈ Finset.univ.erase i, Integrable
      (fun x : (k : Fin n) → N.Var k → ℝ => (N.C i j *ᵥ x j) ⬝ᵥ x i) (Measure.pi σ) :=
    fun j hj => (bilin_exp σ hσ (Finset.ne_of_mem_erase hj) (N.C i j)).1
  refine ⟨h1.1.add (integrable_finsetSum _ h2), ?_⟩
  rw [integral_add h1.1 (integrable_finsetSum _ h2), integral_finsetSum _ h2, h1.2]
  congr 1
  exact Finset.sum_congr rfl
    (fun j hj => (bilin_exp σ hσ (Finset.ne_of_mem_erase hj) (N.C i j)).2)

lemma cost_update_exp (hσ : ∀ i, Integrable id (σ i)) (i : Fin n) (x' : N.Var i → ℝ) :
    Integrable (fun x => N.cost i (Function.update x i x')) (Measure.pi σ) ∧
      ∫ x, N.cost i (Function.update x i x') ∂(Measure.pi σ) =
        N.cost i (Function.update (fun j => ∫ y, y ∂(σ j)) i x') := by
  have he : (fun x => N.cost i (Function.update x i x')) = fun x =>
      N.c i ⬝ᵥ x' + ∑ j ∈ Finset.univ.erase i, (x' ᵥ* N.C i j) ⬝ᵥ x j := by
    funext x; exact cost_update' N i x x'
  rw [he, cost_update' N i]
  have h2 : ∀ j ∈ Finset.univ.erase i, Integrable
      (fun x : (k : Fin n) → N.Var k → ℝ => (x' ᵥ* N.C i j) ⬝ᵥ x j) (Measure.pi σ) :=
    fun j _ => (lin_exp σ hσ j _).1
  refine ⟨(integrable_const _).add (integrable_finsetSum _ h2), ?_⟩
  rw [integral_add (integrable_const _) (integrable_finsetSum _ h2), integral_finsetSum _ h2,
    integral_const]
  simp only [probReal_univ, one_smul]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => (lin_exp σ hσ j _).2)

end CostExp

section Lot

variable {V : Type*} [Fintype V]

lemma lottery_facts (L : Lottery V) (h0 : ∀ j, 0 ≤ L.prob j) (h1 : ∑ j, L.prob j = 1) :
    IsProbabilityMeasure L.measure ∧ Integrable id L.measure ∧
      ∫ y, y ∂L.measure = ∑ j, L.prob j • L.pts j := by
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin L.k)),
      Integrable (id : (V → ℝ) → (V → ℝ)) (ENNReal.ofReal (L.prob j) • Measure.dirac (L.pts j)) :=
    fun j _ => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · unfold Lottery.measure
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h0 j), h1, ENNReal.ofReal_one]
  · unfold Lottery.measure
    exact integrable_finsetSum_measure.mpr hint
  · unfold Lottery.measure
    show ∫ y, id y ∂_ = _
    rw [integral_finsetSum_measure hint]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (h0 j)]
    rfl

lemma lottery_compl (L : Lottery V) (S : Set (V → ℝ))
    (hS : ∀ j, L.prob j ≠ 0 → L.pts j ∈ S) : L.measure Sᶜ = 0 := by
  unfold Lottery.measure
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases hj : L.prob j = 0
  · simp [hj]
  · have : L.pts j ∉ Sᶜ := fun h => h (hS j hj)
    simp [Set.indicator_of_notMem this]

end Lot

/-- Part (b). -/
theorem part_b {n : ℕ} (N : NASP n) (L : (i : Fin n) → Lottery (N.Var i))
    (hL : Alg1Output N (some L)) : IsMNE N.F N.cost (fun i => (L i).measure) := by
  obtain ⟨x, hx, hxi⟩ := hL
  have key : ∀ i, (∀ j, 0 ≤ (L i).prob j) ∧ ∑ j, (L i).prob j = 1 ∧
      ∑ j, (L i).prob j • (L i).pts j = x i ∧ (∀ j, (L i).prob j ≠ 0 → (L i).pts j ∈ N.F i) := by
    intro i
    by_cases hF : x i ∈ N.F i
    · obtain ⟨j0, hp, h1, h0⟩ := (hxi i).1 hF
      have hz : ∀ j, j ≠ j0 → (L i).prob j = 0 := h0
      refine ⟨fun j => ?_, ?_, ?_, fun j hj => ?_⟩
      · by_cases h : j = j0
        · rw [h, h1]; exact zero_le_one
        · rw [hz j h]
      · rw [Finset.sum_eq_single j0 (fun j _ h => hz j h) (by simp), h1]
      · rw [Finset.sum_eq_single j0 (fun j _ h => by rw [hz j h, zero_smul]) (by simp), h1,
          one_smul, hp]
      · by_cases h : j = j0
        · rw [h, hp]; exact hF
        · exact absurd (hz j h) hj
    · obtain ⟨hp, h0, h1, hs⟩ := (hxi i).2 hF
      exact ⟨h0, h1, hs, fun j _ => hp j⟩
  have hfacts := fun i => lottery_facts (L i) (key i).1 (key i).2.1
  have : ∀ i, IsProbabilityMeasure ((L i).measure) := fun i => (hfacts i).1
  have hint : ∀ i, Integrable id ((L i).measure) := fun i => (hfacts i).2.1
  have hmean : (fun j => ∫ y, y ∂((L j).measure)) = x := by
    funext j; rw [(hfacts j).2.2, (key j).2.2.1]
  refine ⟨fun i => ⟨inferInstance, lottery_compl (L i) (N.F i) (key i).2.2.2⟩, fun i => ?_⟩
  have hc := cost_exp N (fun i => (L i).measure) hint i
  refine ⟨hc.1, fun x' hx' => ?_⟩
  have hu := cost_update_exp N (fun i => (L i).measure) hint i x'
  refine ⟨hu.1, ?_⟩
  rw [hc.2, hu.2, hmean]
  exact (hx i).2 x' (subset_closure (subset_convexHull ℝ _ hx'))

/-- Part (c). -/
theorem part_c {n : ℕ} (N : NASP n) (hno : Alg1Output N none) :
    ¬ ∃ σ : (i : Fin n) → Measure (N.Var i → ℝ),
      IsMNE N.F N.cost σ ∧ ∀ i, Integrable id (σ i) := by
  rintro ⟨σ, ⟨hσ1, hσ2⟩, hint⟩
  have : ∀ i, IsProbabilityMeasure (σ i) := fun i => (hσ1 i).1
  apply hno
  refine ⟨fun j => ∫ y, y ∂(σ j), fun i => ⟨?_, ?_⟩⟩
  · refine Convex.integral_mem ((convex_convexHull ℝ _).closure) isClosed_closure ?_ (hint i)
    have h0 : ∀ᵐ a ∂(σ i), a ∉ (N.F i)ᶜ := measure_eq_zero_iff_ae_notMem.mp (hσ1 i).2
    filter_upwards [h0] with a ha
    exact subset_closure (subset_convexHull ℝ _ (not_not.mp ha))
  · set m : (j : Fin n) → N.Var j → ℝ := fun j => ∫ y, y ∂(σ j) with hm
    set v : N.Var i → ℝ := N.c i + ∑ j ∈ Finset.univ.erase i, N.C i j *ᵥ m j with hv
    have hS : N.F i ⊆ {x' | N.cost i m ≤ v ⬝ᵥ x'} := by
      intro x' hx'
      have hc := cost_exp N σ hint i
      have hu := cost_update_exp N σ hint i x'
      have h := ((hσ2 i).2 x' hx').2
      rw [hc.2, hu.2, cost_update] at h
      exact h
    have hconv : Convex ℝ {x' : N.Var i → ℝ | N.cost i m ≤ v ⬝ᵥ x'} :=
      convex_halfSpace_ge ⟨fun a b => dotProduct_add v a b, fun c a => dotProduct_smul c v a⟩ _
    have hcl : IsClosed {x' : N.Var i → ℝ | N.cost i m ≤ v ⬝ᵥ x'} :=
      isClosed_le continuous_const (continuous_const.dotProduct continuous_id)
    intro x' hx'
    have := closure_minimal (convexHull_min hS hconv) hcl hx'
    rw [cost_update]
    exact this

end NashStackelberg

namespace NashStackelberg

/-! ## Balas: the closed convex hull of a finite union of polyhedra -/

lemma IsPoly.isClosed {ι : Type} [Fintype ι] {S : Set (ι → ℝ)} (h : IsPoly S) :
    IsClosed S := by
  obtain ⟨r, A, b, rfl⟩ := h
  exact isClosed_le (Matrix.mulVecLin A).continuous_of_finiteDimensional continuous_const

lemma IsPoly.convex {ι : Type} [Fintype ι] {S : Set (ι → ℝ)} (h : IsPoly S) :
    Convex ℝ S := by
  obtain ⟨r, A, b, rfl⟩ := h
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_setOf_eq, Pi.le_def] at hx hy ⊢
  intro j
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : a * b j + c * b j = b j := by rw [← add_mul, hac, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left (hx j) ha, mul_le_mul_of_nonneg_left (hy j) hc]

lemma balas {ι Θ : Type} [Fintype ι] [Fintype Θ] [DecidableEq ι] (m : Θ → ℕ)
    (A : ∀ θ, Matrix (Fin (m θ)) ι ℝ) (b : ∀ θ, Fin (m θ) → ℝ) :
    IsPoly (closure (convexHull ℝ (⋃ θ, {x | A θ *ᵥ x ≤ b θ}))) := by
  classical
  let P : Θ → Set (ι → ℝ) := fun θ => {x | A θ *ᵥ x ≤ b θ}
  let T := {θ : Θ // (P θ).Nonempty}
  let S : Set ((ι ⊕ ((T × ι) ⊕ T)) → ℝ) :=
    (⋂ a : ι, {z | z (.inl a) = ∑ t : T, z (.inr (.inl (t, a)))}) ∩
    (⋂ t : T, {z | A t.1 *ᵥ (fun a => z (.inr (.inl (t, a)))) ≤ z (.inr (.inr t)) • b t.1}) ∩
    (⋂ t : T, {z | 0 ≤ z (.inr (.inr t))}) ∩
    {z | ∑ t : T, z (.inr (.inr t)) = 1}
  have hS : IsPoly S := by
    refine (((isPoly_iInter _ fun a => ?_).inter (isPoly_iInter _ fun t => ?_)).inter
      (isPoly_iInter _ fun t => ?_)).inter ?_
    · convert isPoly_eq_fun (LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) (Sum.inl a) -
        ∑ t : T, LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) (Sum.inr (Sum.inl (t, a)))) 0 using 1
      ext z
      simp [LinearMap.sum_apply, sub_eq_zero]
      all_goals infer_instance
    · convert isPoly_le_lin ((A t.1).mulVecLin ∘ₗ
        LinearMap.pi (fun a => LinearMap.proj (R := ℝ) (φ := fun _ => ℝ)
          (Sum.inr (Sum.inl (t, a)))) -
        LinearMap.smulRight (LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) (Sum.inr (Sum.inr t)))
          (b t.1)) 0 using 1
      ext z
      simp only [Set.mem_setOf_eq, Pi.le_def, LinearMap.sub_apply, LinearMap.comp_apply,
        Matrix.mulVecLin_apply, LinearMap.smulRight_apply, Pi.sub_apply, Pi.zero_apply,
        sub_nonpos, Pi.smul_apply, Matrix.mulVec, dotProduct, LinearMap.pi_apply,
        LinearMap.proj_apply]
      all_goals infer_instance
    · convert isPoly_le_fun (-(LinearMap.proj (R := ℝ) (φ := fun _ => ℝ)
        (Sum.inr (Sum.inr t)))) 0 using 1
      ext z
      simp
      all_goals infer_instance
    · convert isPoly_eq_fun (∑ t : T, LinearMap.proj (R := ℝ) (φ := fun _ => ℝ)
        (Sum.inr (Sum.inr t))) 1 using 1
      ext z
      simp [LinearMap.sum_apply]
      all_goals infer_instance
  have hQ := hS.proj
  convert hQ using 1
  apply Set.Subset.antisymm
  · refine closure_minimal (convexHull_min ?_ hQ.convex) hQ.isClosed
    intro x hx
    obtain ⟨θ, hxθ⟩ := Set.mem_iUnion.1 hx
    let t0 : T := ⟨θ, x, hxθ⟩
    refine ⟨Sum.elim (fun q : T × ι => if q.1 = t0 then x q.2 else 0)
      (fun t => if t = t0 then 1 else 0), ?_⟩
    simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Sum.elim_inl,
      Sum.elim_inr]
    refine ⟨⟨⟨fun a => ?_, fun t => ?_⟩, fun t => ?_⟩, ?_⟩
    · rw [Finset.sum_ite_eq']; simp
    · by_cases ht : t = t0
      · subst ht; simpa using hxθ
      · simp [ht]
        intro j
        simp [Matrix.mulVec, dotProduct]
    · by_cases ht : t = t0 <;> simp [ht]
    · rw [Finset.sum_ite_eq']; simp
  · rintro x ⟨u, hu⟩
    simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Sum.elim_inl,
      Sum.elim_inr] at hu
    obtain ⟨⟨⟨hsum, hA⟩, hlam0⟩, hlam1⟩ := hu
    set xs : T → ι → ℝ := fun t a => u (.inl (t, a))
    set lam : T → ℝ := fun t => u (.inr t)
    have hTne : Nonempty T := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hlam1
    set nT : ℝ := (Fintype.card T : ℝ)
    have hnT : 0 < nT := by
      simp only [nT]; exact_mod_cast Fintype.card_pos
    let p : T → ι → ℝ := fun t => t.2.some
    have hp : ∀ t, A t.1 *ᵥ p t ≤ b t.1 := fun t => t.2.some_mem
    have hxs : ∑ t, xs t = x := by
      funext a; rw [Finset.sum_apply]; exact (hsum a).symm
    let f : ℝ → (ι → ℝ) := fun ε => (1 - ε) • x + (ε / nT) • ∑ t, p t
    have hf : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
      have hc : Continuous f := by fun_prop
      exact (hc.tendsto' 0 x (by simp [f])).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    refine mem_closure_of_tendsto hf ?_
    have hlt : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), ε < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt] with ε hε0 hε1
    have hε0 : (0:ℝ) < ε := hε0
    set μ : T → ℝ := fun t => (1 - ε) * lam t + ε / nT
    have hμ : ∀ t, 0 < μ t := fun t => by
      have := hlam0 t
      have : 0 < ε / nT := div_pos hε0 hnT
      simp only [μ]; nlinarith
    let z : T → ι → ℝ := fun t => (μ t)⁻¹ • ((1 - ε) • xs t + (ε / nT) • p t)
    have hsumμ : ∑ t, μ t = 1 := by
      simp only [μ, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      have : ∑ t, lam t = 1 := hlam1
      rw [this]; field_simp; ring
    have hfz : f ε = ∑ t, μ t • z t := by
      simp only [z, smul_smul]
      have : ∀ t, μ t * (μ t)⁻¹ = 1 := fun t => mul_inv_cancel₀ (hμ t).ne'
      simp only [this, one_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hxs, f]
    rw [hfz]
    refine (convex_convexHull ℝ _).sum_mem (fun t _ => (hμ t).le) hsumμ fun t _ => ?_
    apply subset_convexHull
    refine Set.mem_iUnion.2 ⟨t.1, ?_⟩
    simp only [Set.mem_setOf_eq, Pi.le_def]
    intro j
    simp only [z, Matrix.mulVec_smul, Matrix.mulVec_add, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul]
    have h1 := hA t j
    have h2 := hp t j
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have hle : (1 - ε) * (A t.1 *ᵥ xs t) j + ε / nT * (A t.1 *ᵥ p t) j ≤ μ t * b t.1 j := by
      have : 0 ≤ 1 - ε := by linarith
      have : 0 ≤ ε / nT := (div_pos hε0 hnT).le
      simp only [μ]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - ε),
        mul_le_mul_of_nonneg_left h2 this]
    calc (μ t)⁻¹ * ((1 - ε) * (A t.1 *ᵥ xs t) j + ε / nT * (A t.1 *ᵥ p t) j)
        ≤ (μ t)⁻¹ * (μ t * b t.1 j) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (hμ t).le)
      _ = b t.1 j := by rw [← mul_assoc, inv_mul_cancel₀ (hμ t).ne', one_mul]

theorem part_a2 {n : ℕ} (N : NASP n) (i : Fin n) :
    ∃ (p r : ℕ) (A : Matrix (Fin r) (N.Var i) ℝ) (B : Matrix (Fin r) (Fin p) ℝ)
      (b : Fin r → ℝ), N.Ftilde i = {x | ∃ u, A *ᵥ x + B *ᵥ u ≤ b} := by
  obtain ⟨m, A, b, hF⟩ := part_a1 N i
  obtain ⟨r, A', b', h⟩ := balas m A b
  refine ⟨0, r, A', 0, b', ?_⟩
  rw [NASP.Ftilde, hF, h]
  ext x
  simp

/-! ## (d): decomposing a point of conv(F) over the 2^rows convex pieces -/

lemma conv_decomp {E Θ : Type} [AddCommGroup E] [Module ℝ E] [Fintype Θ] (s : Θ → Set E)
    (hs : ∀ θ, Convex ℝ (s θ)) (f0 : E) (hf0 : f0 ∈ ⋃ θ, s θ) {y : E}
    (hy : y ∈ convexHull ℝ (⋃ θ, s θ)) :
    ∃ (μ : Θ → ℝ) (z : Θ → E), (∀ θ, 0 ≤ μ θ) ∧ ∑ θ, μ θ = 1 ∧
      (∀ θ, z θ ∈ ⋃ θ, s θ) ∧ ∑ θ, μ θ • z θ = y := by
  classical
  obtain ⟨κ, _, w, z, hw0, hw1, hz, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hy
  choose θj hθj using fun j => Set.mem_iUnion.1 (hz j)
  let μ : Θ → ℝ := fun θ => ∑ j ∈ Finset.univ.filter (fun j => θj j = θ), w j
  let z' : Θ → E := fun θ => if μ θ = 0 then f0 else
    ∑ j ∈ Finset.univ.filter (fun j => θj j = θ), (w j / μ θ) • z j
  have hμ0 : ∀ θ, 0 ≤ μ θ := fun θ => Finset.sum_nonneg fun j _ => hw0 j
  refine ⟨μ, z', hμ0, ?_, fun θ => ?_, ?_⟩
  · rw [Finset.sum_fiberwise Finset.univ θj w]; exact hw1
  · by_cases h : μ θ = 0
    · simp only [z', h, if_true]; exact hf0
    · have : z' θ ∈ s θ := by
        simp only [z', h, if_false]
        apply (hs θ).sum_mem
        · intro j _; exact div_nonneg (hw0 j) (hμ0 θ)
        · rw [← Finset.sum_div]; exact div_self h
        · intro j hj
          have := (Finset.mem_filter.1 hj).2
          rw [← this]; exact hθj j
      exact Set.mem_iUnion.2 ⟨θ, this⟩
  · have key : ∀ θ, μ θ • z' θ = ∑ j ∈ Finset.univ.filter (fun j => θj j = θ), w j • z j := by
      intro θ
      by_cases h : μ θ = 0
      · simp only [z', h, if_true, zero_smul]
        symm; apply Finset.sum_eq_zero; intro j hj
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw0 j)).1 h j hj
        rw [this, zero_smul]
      · simp only [z', h, if_false, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_div_cancel₀ _ h]
    simp only [key]
    exact Finset.sum_fiberwise Finset.univ θj (fun j => w j • z j)

theorem part_d {n : ℕ} (N : NASP n) (hcl : ∀ i, IsClosed (convexHull ℝ (N.F i))) :
    ∃ out, Alg1Output N out ∧ ∀ L, out = some L → ∀ i, (L i).k ≤ 2 ^ N.rows i := by
  classical
  by_cases hx : ∃ x, IsPNE N.Ftilde N.cost x
  swap
  · exact ⟨none, hx, fun L h => by cases h⟩
  obtain ⟨x, hx⟩ := hx
  have key : ∀ i, ∃ Li : Lottery (N.Var i), Li.k ≤ 2 ^ N.rows i ∧
      (x i ∈ N.F i →
        ∃ j, Li.pts j = x i ∧ Li.prob j = 1 ∧ ∀ j', j' ≠ j → Li.prob j' = 0) ∧
      (x i ∉ N.F i →
        (∀ j, Li.pts j ∈ N.F i) ∧ (∀ j, 0 ≤ Li.prob j) ∧ ∑ j, Li.prob j = 1 ∧
          ∑ j, Li.prob j • Li.pts j = x i) := by
    intro i
    by_cases hxi : x i ∈ N.F i
    · refine ⟨⟨1, fun _ => x i, fun _ => 1⟩, Nat.one_le_two_pow,
        fun _ => ⟨0, rfl, rfl, fun j' hj' => absurd (Subsingleton.elim j' 0) hj'⟩,
        fun h => absurd hxi h⟩
    · have hmem : x i ∈ convexHull ℝ (N.F i) := by
        have := (hx i).1
        rw [NASP.Ftilde, (hcl i).closure_eq] at this
        exact this
      obtain ⟨m, A, b, hF⟩ := part_a1 N i
      obtain ⟨f0, hf0⟩ : (N.F i).Nonempty := by
        by_contra h
        rw [Set.not_nonempty_iff_eq_empty] at h
        rw [h, convexHull_empty] at hmem
        exact hmem
      rw [hF] at hmem hf0
      obtain ⟨μ, z, hμ0, hμ1, hz, hsum⟩ := conv_decomp (fun θ => {x | A θ *ᵥ x ≤ b θ})
        (fun θ => IsPoly.convex ⟨m θ, A θ, b θ, rfl⟩) f0 hf0 hmem
      let E : Fin (2 ^ N.rows i) ≃ (Fin (N.rows i) → Bool) :=
        (Fintype.equivFinOfCardEq (by simp)).symm
      refine ⟨⟨2 ^ N.rows i, fun j => z (E j), fun j => μ (E j)⟩, le_rfl,
        fun h => absurd h hxi, fun _ => ⟨fun j => ?_, fun j => hμ0 _, ?_, ?_⟩⟩
      · rw [hF]; exact hz _
      · exact (E.sum_comp μ).trans hμ1
      · exact (E.sum_comp (fun θ => μ θ • z θ)).trans hsum
  choose L hLk hL1 hL2 using key
  exact ⟨some L, ⟨x, hx, fun i => ⟨hL1 i, hL2 i⟩⟩, fun L' hL' i => by cases hL'; exact hLk i⟩

end NashStackelberg

open NashStackelberg MeasureTheory Matrix in
theorem solution {n : ℕ} (N : NASP n) :
    (∀ i, (∃ (m : (Fin (N.rows i) → Bool) → ℕ)
        (A : (θ : Fin (N.rows i) → Bool) → Matrix (Fin (m θ)) (N.Var i) ℝ)
        (b : (θ : Fin (N.rows i) → Bool) → Fin (m θ) → ℝ),
        N.F i = ⋃ θ, {x | A θ *ᵥ x ≤ b θ}) ∧
      (∃ (p r : ℕ) (A : Matrix (Fin r) (N.Var i) ℝ) (B : Matrix (Fin r) (Fin p) ℝ)
        (b : Fin r → ℝ), N.Ftilde i = {x | ∃ u, A *ᵥ x + B *ᵥ u ≤ b})) ∧
    (∀ L, Alg1Output N (some L) → IsMNE N.F N.cost (fun i => (L i).measure)) ∧
    (Alg1Output N none → ¬ ∃ σ : (i : Fin n) → Measure (N.Var i → ℝ),
      IsMNE N.F N.cost σ ∧ ∀ i, Integrable id (σ i)) ∧
    ((∀ i, IsClosed (convexHull ℝ (N.F i))) →
      ∃ out, Alg1Output N out ∧ ∀ L, out = some L → ∀ i, (L i).k ≤ 2 ^ N.rows i) := by
  exact ⟨fun i => ⟨part_a1 N i, part_a2 N i⟩, fun L hL => part_b N L hL, part_c N, part_d N⟩
