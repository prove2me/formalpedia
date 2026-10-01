-- Prove2me | solution 1 for MurtyKabadi.Reduction.box_minimum_integer_minor_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T09:30:43.866534+00:00
-- url     : https://prove2.me/submissions/e5fdfe4c-5c84-4007-a309-4a95ec1d5793

import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

open MurtyKabadi.Reduction Matrix
open scoped Topology

private lemma q_add_smul {m : ℕ} (D : Matrix (Fin m) (Fin m) ℝ)
    (hD : D.IsSymm) (x v : Fin m → ℝ) (t : ℝ) :
    Q D (x + t • v) = Q D x + 2 * t * (v ⬝ᵥ (D *ᵥ x)) + t ^ 2 * Q D v := by
  have hcross : x ⬝ᵥ (D *ᵥ v) = v ⬝ᵥ (D *ᵥ x) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hD, dotProduct_comm]
  simp only [Q, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hcross]
  ring

private lemma line_feasible {m : ℕ} (x v : Fin m → ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hv : ∀ i, v i ≠ 0 → 0 < x i ∧ x i < 1) :
    ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ x + t • v ∧ x + t • v ≤ 1 := by
  have hi (i : Fin m) : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ x i + t * v i ∧ x i + t * v i ≤ 1 := by
    by_cases hvi : v i = 0
    · exact Filter.Eventually.of_forall (fun _ => by simpa [hvi] using And.intro (hx0 i) (hx1 i))
    · have hc : Continuous (fun t : ℝ => x i + t * v i) := by fun_prop
      have hc0 : ContinuousAt (fun t : ℝ => x i + t * v i) 0 := hc.continuousAt
      have ht : ∀ᶠ t : ℝ in 𝓝 0, x i + t * v i ∈ Set.Ioo 0 1 :=
        hc0.eventually (Ioo_mem_nhds (by simpa using (hv i hvi).1)
          (by simpa using (hv i hvi).2))
      filter_upwards [ht] with t ht
      exact ⟨ht.1.le, ht.2.le⟩
  filter_upwards [Filter.eventually_all.mpr hi] with t ht
  exact ⟨fun i => (ht i).1, fun i => (ht i).2⟩

private lemma stationary_direction {m : ℕ} (D : Matrix (Fin m) (Fin m) ℝ)
    (hD : D.IsSymm) (x v : Fin m → ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hmin : ∀ z, 0 ≤ z → z ≤ 1 → Q D x ≤ Q D z)
    (hv : ∀ i, v i ≠ 0 → 0 < x i ∧ x i < 1) :
    v ⬝ᵥ (D *ᵥ x) = 0 := by
  have hloc : IsLocalMin (fun t : ℝ =>
      Q D x + 2 * t * (v ⬝ᵥ (D *ᵥ x)) + t ^ 2 * Q D v) 0 := by
    filter_upwards [line_feasible x v hx0 hx1 hv] with t ht
    simpa only [q_add_smul D hD x v t, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
      add_zero] using hmin (x + t • v) ht.1 ht.2
  have hd : HasDerivAt (fun t : ℝ =>
      Q D x + 2 * t * (v ⬝ᵥ (D *ᵥ x)) + t ^ 2 * Q D v)
      (2 * (v ⬝ᵥ (D *ᵥ x))) 0 := by
    convert! (((hasDerivAt_const (0 : ℝ) (Q D x)).add
      (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (v ⬝ᵥ (D *ᵥ x)))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (Q D v))) using 1
    simp
  have := hloc.hasDerivAt_eq_zero hd
  linarith

private lemma sum_support {m : ℕ} (S : Finset (Fin m)) (f : Fin m → ℝ)
    (hf : ∀ i, i ∉ S → f i = 0) : (∑ i, f i) = ∑ i : S, f i.1 := by
  rw [Finset.sum_coe_sort]
  symm
  exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hf i hi)

private lemma restricted_mulVec {m : ℕ} (D : Matrix (Fin m) (Fin m) ℝ)
    (S : Finset (Fin m)) (v : Fin m → ℝ) (hv : ∀ i, i ∉ S → v i = 0) (i : S) :
    (D *ᵥ v) i.1 =
      ((D.submatrix (fun j : S => j.1) (fun j : S => j.1)) *ᵥ (fun j : S => v j.1)) i := by
  exact sum_support S (fun j => D i.1 j * v j) (fun j hj => by rw [hv j hj, mul_zero])

private lemma stationary_coordinate {m : ℕ} (D : Matrix (Fin m) (Fin m) ℝ)
    (hD : D.IsSymm) (x : Fin m → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hmin : ∀ z, 0 ≤ z → z ≤ 1 → Q D x ≤ Q D z)
    (i : Fin m) (hi : 0 < x i ∧ x i < 1) : (D *ᵥ x) i = 0 := by
  have h := stationary_direction D hD x (Pi.single i 1) hx0 hx1 hmin (by
    intro j hj
    by_cases hji : j = i
    · simpa [hji] using hi
    · exact False.elim (hj (by simp [hji])))
  simpa using h

private lemma exists_nonsingular_box_minimizer {m : ℕ}
    (D : Matrix (Fin m) (Fin m) ℝ) (hD : D.IsSymm)
    (x : Fin m → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hmin : ∀ z, 0 ≤ z → z ≤ 1 → Q D x ≤ Q D z) :
    ∃ y : Fin m → ℝ, ∃ S : Finset (Fin m),
      (0 ≤ y ∧ y ≤ 1) ∧ Q D y = Q D x ∧
      (∀ i, i ∈ S ↔ 0 < y i ∧ y i < 1) ∧
      (D.submatrix (fun i : S => i.1) (fun i : S => i.1)).det ≠ 0 := by
  classical
  let K : Set (Fin m → ℝ) := Set.Icc 0 1 ∩ {y | Q D y = Q D x}
  have hqcont : Continuous (Q D) := by unfold Q Matrix.mulVec dotProduct; fun_prop
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_eq hqcont continuous_const)
  have hxK : x ∈ K := ⟨⟨hx0, hx1⟩, rfl⟩
  let N : (Fin m → ℝ) → ℝ := fun z => ∑ i, (z i) ^ 2
  have hN : Continuous N := by dsimp [N]; fun_prop
  obtain ⟨y, hyK, hmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hN.continuousOn
  have hymin : ∀ z, 0 ≤ z → z ≤ 1 → Q D y ≤ Q D z := by
    intro z hz0 hz1
    rw [hyK.2]
    exact hmin z hz0 hz1
  let S : Finset (Fin m) := Finset.univ.filter (fun i => 0 < y i ∧ y i < 1)
  have hS (i : Fin m) : i ∈ S ↔ 0 < y i ∧ y i < 1 := by simp [S]
  refine ⟨y, S, hyK.1, hyK.2, hS, ?_⟩
  intro hdet
  obtain ⟨d, hdne, hd⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let v : Fin m → ℝ := fun i => if hi : i ∈ S then d ⟨i, hi⟩ else 0
  have hvs (i : S) : v i.1 = d i := by simp [v, i.property]
  have hvo (i : Fin m) (hi : i ∉ S) : v i = 0 := by simp [v, hi]
  have hv : ∀ i, v i ≠ 0 → 0 < y i ∧ y i < 1 := by
    intro i hi
    apply (hS i).mp
    by_contra hiS
    exact hi (hvo i hiS)
  have hvne : v ≠ 0 := by
    intro hz
    apply hdne
    funext i
    simpa only [hvs, Pi.zero_apply] using congrFun hz i.1
  have hrow (i : S) : (D *ᵥ v) i.1 = 0 := by
    rw [restricted_mulVec D S v hvo i]
    simpa only [hvs, Pi.zero_apply] using congrFun hd i
  have hqv : Q D v = 0 := by
    unfold Q dotProduct
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ S
    · simp [hrow ⟨i, hi⟩]
    · simp [hvo i hi]
  have hstat := stationary_direction D hD y v hyK.1.1 hyK.1.2 hymin hv
  have hflat (t : ℝ) : Q D (y + t • v) = Q D y := by
    rw [q_add_smul D hD, hstat, hqv]
    ring
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp
    (line_feasible y v hyK.1.1 hyK.1.2 hv)
  let t : ℝ := ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htε : t < ε := by dsimp [t]; linarith
  have hplus := he (y := t) (by simpa [Real.dist_eq, abs_of_pos ht] using htε)
  have hminus := he (y := -t) (by simpa [Real.dist_eq, abs_neg, abs_of_pos ht] using htε)
  have hp : N (y + t • v) ≤ N y := hmax ⟨hplus, (hflat t).trans hyK.2⟩
  have hm : N (y + (-t) • v) ≤ N y := hmax ⟨hminus, (hflat (-t)).trans hyK.2⟩
  have hn (a : ℝ) : N (y + a • v) = N y + 2 * a * (∑ i, y i * v i) + a ^ 2 * N v := by
    dsimp [N]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hNv : 0 < N v := by
    apply Finset.sum_pos' (fun i _ => sq_nonneg (v i))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hvne
    exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  rw [hn] at hp hm
  have hpos : 0 < t ^ 2 * N v := mul_pos (sq_pos_of_pos ht) hNv
  nlinarith

theorem solution
    {m : ℕ} (D : Matrix (Fin m) (Fin m) ℤ) (hD : D.IsSymm)
    (x : Fin m → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hmin : ∀ z : Fin m → ℝ, 0 ≤ z → z ≤ 1 →
      Q (D.map (Int.cast : ℤ → ℝ)) x ≤ Q (D.map (Int.cast : ℤ → ℝ)) z) :
    ∃ S : Finset (Fin m),
      (D.submatrix (fun i : S => i.1) (fun i : S => i.1)).det ≠ 0 ∧
      ∃ a : ℤ, Q (D.map (Int.cast : ℤ → ℝ)) x *
        ((D.submatrix (fun i : S => i.1) (fun i : S => i.1)).det : ℝ) = (a : ℝ) := by
  classical
  let E : Matrix (Fin m) (Fin m) ℝ := D.map (Int.cast : ℤ → ℝ)
  have hE : E.IsSymm := hD.map _
  obtain ⟨y, S, hybox, hyval, hS, hdet⟩ :=
    exists_nonsingular_box_minimizer E hE x hx0 hx1 hmin
  let A : Matrix S S ℤ := D.submatrix (fun i : S => i.1) (fun i : S => i.1)
  let B : Matrix S S ℝ := A.map (Int.cast : ℤ → ℝ)
  have hdetcast : (A.det : ℝ) = B.det := (Int.castRingHom ℝ).map_det A
  have hk : A.det ≠ 0 := by
    intro hz
    apply hdet
    change B.det = 0
    rw [← hdetcast, hz]
    simp
  refine ⟨S, hk, ?_⟩
  have hymin : ∀ z, 0 ≤ z → z ≤ 1 → Q E y ≤ Q E z := by
    intro z hz0 hz1
    rw [hyval]
    exact hmin z hz0 hz1
  have hstat (i : Fin m) (hi : i ∈ S) : (E *ᵥ y) i = 0 :=
    stationary_coordinate E hE y hybox.1 hybox.2 hymin i ((hS i).mp hi)
  have hout (i : Fin m) (hi : i ∉ S) : y i = 0 ∨ y i = 1 := by
    by_cases h0 : y i = 0
    · exact Or.inl h0
    · right
      by_contra h1
      apply hi
      exact (hS i).mpr ⟨lt_of_le_of_ne (hybox.1 i) (Ne.symm h0),
        lt_of_le_of_ne (hybox.2 i) h1⟩
  let u : Fin m → ℤ := fun i => if i ∈ S then 0 else if y i = 1 then 1 else 0
  have hus (i : S) : u i.1 = 0 := by simp [u, i.property]
  have huo (i : Fin m) (hi : i ∉ S) : (u i : ℝ) = y i := by
    rcases hout i hi with h | h <;> simp [u, hi, h]
  let ur : Fin m → ℝ := fun i => (u i : ℝ)
  let r : Fin m → ℝ := y - ur
  have hro (i : Fin m) (hi : i ∉ S) : r i = 0 := by simp [r, ur, huo i hi]
  have hrs (i : S) : r i.1 = y i.1 := by simp [r, ur, hus i]
  let b : S → ℤ := fun i => -(D *ᵥ u) i.1
  have hsys : B *ᵥ (fun i : S => y i.1) = (fun i : S => (b i : ℝ)) := by
    funext i
    have hrow := restricted_mulVec E S r hro i
    have hur : (E *ᵥ ur) i.1 = ((D *ᵥ u) i.1 : ℝ) := by
      simp [E, ur, Matrix.mulVec, dotProduct]
    have hre : (E *ᵥ r) i.1 = -((D *ᵥ u) i.1 : ℝ) := by
      rw [show r = y - ur from rfl, mulVec_sub, Pi.sub_apply, hstat i.1 i.property, hur]
      ring
    change (B *ᵥ (fun i : S => y i.1)) i = (b i : ℝ)
    rw [show (fun i : S => y i.1) = (fun i : S => r i.1) by funext i; exact (hrs i).symm]
    change ((E.submatrix (fun i : S => i.1) (fun i : S => i.1)) *ᵥ
      (fun i : S => r i.1)) i = (b i : ℝ)
    rw [← hrow, hre]
    simp [b]
  have hadj := congrArg (fun v : S → ℝ => B.adjugate *ᵥ v) hsys
  rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, ← hdetcast] at hadj
  have hAadj : B.adjugate = A.adjugate.map (Int.cast : ℤ → ℝ) := by
    exact ((Int.castRingHom ℝ).map_adjugate A).symm
  let c : Fin m → ℤ := fun i => if hi : i ∈ S then (A.adjugate *ᵥ b) ⟨i, hi⟩ else A.det * u i
  have hscale (i : Fin m) : (A.det : ℝ) * y i = (c i : ℝ) := by
    by_cases hi : i ∈ S
    · have he := congrFun hadj ⟨i, hi⟩
      rw [hAadj] at he
      simpa [c, hi, Matrix.mulVec, dotProduct] using he
    · simp [c, hi, ← huo i hi]
  let a : ℤ := u ⬝ᵥ (D *ᵥ c)
  refine ⟨a, ?_⟩
  change Q E x * (A.det : ℝ) = (a : ℝ)
  rw [← hyval]
  have hq : Q E y = ur ⬝ᵥ (E *ᵥ y) := by
    unfold Q dotProduct
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · simp [hstat i hi]
    · rw [show ur i = y i from huo i hi]
  rw [hq]
  simp only [dotProduct, Matrix.mulVec, E, Matrix.map_apply, ur, a,
    Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, mul_comm (y j), hscale j]
