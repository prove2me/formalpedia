-- Prove2me | solution 1 for Gomory69.Asymptotic.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:04:29.566836+00:00
-- url     : https://prove2.me/submissions/b33aed2a-f515-4a2e-ac32-43c8da31a889

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram



namespace Gomory69.Asymptotic
open Matrix


theorem thm1_core {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∏ g : ↥𝒩, (1 + t g) ≤ Fintype.card G := by
  classical
  let S : Finset (↥𝒩 → ℕ) := Fintype.piFinset (fun g => Finset.range (t g + 1))
  have hcard : S.card = ∏ g : ↥𝒩, (1 + t g) := by
    simp [S, Fintype.card_piFinset, add_comm]
  let φ : (↥𝒩 → ℕ) → G := fun s => ∑ g, s g • (g : G)
  have hinj : Set.InjOn φ S := by
    intro s hs r hr h
    simp only [S, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range] at hs hr
    have := ht (fun g => (r g : ℤ)) (fun g => (s g : ℤ))
      (fun g => ⟨by positivity, by have := hr g; omega⟩)
      (fun g => ⟨by positivity, by have := hs g; omega⟩)
      (by simpa [φ, natCast_zsmul] using h.symm)
    funext g
    have := congrFun this g
    simpa using this
  have : S.card ≤ (Finset.univ : Finset G).card :=
    Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) hinj
  rw [← hcard]; simpa using this

theorem one_add_sum_le_prod {ι : Type*} [Fintype ι] (t : ι → ℕ) :
    1 + ∑ i, t i ≤ ∏ i, (1 + t i) := by
  classical
  have : ∀ s : Finset ι, 1 + ∑ i ∈ s, t i ≤ ∏ i ∈ s, (1 + t i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      nlinarith [Nat.zero_le (t a), Nat.zero_le (∑ i ∈ s, t i)]
  exact this Finset.univ

theorem sum_le_core {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∑ g : ↥𝒩, t g ≤ Fintype.card G - 1 := by
  have h1 := thm1_core 𝒩 h𝒩 t ht
  have h2 := one_add_sum_le_prod t
  omega

theorem thm2_core {G : Type*} [AddCommGroup G] [Finite G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (g₀ : G) (v : ↥𝒩 → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (groupPolyhedron 𝒩 g₀)) :
    ∃ t ∈ groupSolutions 𝒩 g₀, toReal 𝒩 t = v ∧ IsIrreducible 𝒩 t := by
  classical
  have hv' := hv
  have hmem := extremePoints_convexHull_subset hv
  obtain ⟨t, ht, rfl⟩ := hmem
  refine ⟨t, ht, rfl, ?_⟩
  intro s r hs hr hsr
  by_contra hne
  set d : ↥𝒩 → ℤ := fun g => r g - s g with hd
  let t1 : ↥𝒩 → ℕ := fun g => ((t g : ℤ) + d g).toNat
  let t2 : ↥𝒩 → ℕ := fun g => ((t g : ℤ) - d g).toNat
  have h1 : ∀ g, (t1 g : ℤ) = t g + d g := fun g => by
    have := hs g; have := hr g; simp only [t1, hd]; omega
  have h2 : ∀ g, (t2 g : ℤ) = t g - d g := fun g => by
    have := hs g; have := hr g; simp only [t2, hd]; omega
  have hsum : ∑ g : ↥𝒩, d g • (g : G) = 0 := by
    simp only [hd, sub_smul, Finset.sum_sub_distrib]; rw [hsr]; simp
  have hs1 : t1 ∈ groupSolutions 𝒩 g₀ := by
    unfold groupSolutions at ht ⊢
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [← ht]
    have : ∀ g : ↥𝒩, t1 g • (g : G) = t g • (g : G) + d g • (g : G) := fun g => by
      rw [← natCast_zsmul, h1, add_smul, natCast_zsmul]
    simp only [this, Finset.sum_add_distrib, hsum, add_zero]
  have hs2 : t2 ∈ groupSolutions 𝒩 g₀ := by
    unfold groupSolutions at ht ⊢
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [← ht]
    have : ∀ g : ↥𝒩, t2 g • (g : G) = t g • (g : G) - d g • (g : G) := fun g => by
      rw [← natCast_zsmul, h2, sub_smul, natCast_zsmul]
    simp only [this, Finset.sum_sub_distrib, hsum, sub_zero]
  have hP1 : toReal 𝒩 t1 ∈ groupPolyhedron 𝒩 g₀ := subset_convexHull ℝ _ ⟨t1, hs1, rfl⟩
  have hP2 : toReal 𝒩 t2 ∈ groupPolyhedron 𝒩 g₀ := subset_convexHull ℝ _ ⟨t2, hs2, rfl⟩
  have hseg : toReal 𝒩 t ∈ openSegment ℝ (toReal 𝒩 t1) (toReal 𝒩 t2) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext g
    have a := h1 g; have b := h2 g
    have a' : (t1 g : ℝ) = t g + d g := by exact_mod_cast a
    have b' : (t2 g : ℝ) = t g - d g := by exact_mod_cast b
    simp only [toReal, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a', b']
    ring
  have := hv'.2 hP1 hP2 hseg
  apply hne
  funext g
  have := congrFun this g
  simp only [toReal] at this
  have a' : (t1 g : ℝ) = t g + d g := by exact_mod_cast h1 g
  have : (d g : ℝ) = 0 := by linarith
  have : d g = 0 := by exact_mod_cast this
  simp only [hd] at this; omega




theorem lattice_eq_range {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) :
    basisLattice B = (LinearMap.range (Matrix.mulVecLin B)).toAddSubgroup := by
  apply le_antisymm
  · unfold basisLattice
    rw [AddSubgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    funext i
    simp [Matrix.mulVec_single_one]
  · rintro _ ⟨x, rfl⟩
    have : Matrix.mulVecLin B x = ∑ j, x j • (fun i => B i j) := by
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    show Matrix.mulVecLin B x ∈ basisLattice B
    rw [this]
    refine AddSubgroup.sum_mem _ (fun j _ => ?_)
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self j)) _

theorem card_factor_core {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) :
    Finite (FactorGroup B) ∧ Nat.card (FactorGroup B) = detAbs B := by
  have hinj : Function.Injective (Matrix.mulVecLin B) := by
    intro x y hxy
    have : B.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet this
    exact sub_eq_zero.mp h2
  let e : (Fin m → ℤ) ≃ₗ[ℤ] LinearMap.range (Matrix.mulVecLin B) :=
    LinearEquiv.ofInjective (Matrix.mulVecLin B) hinj
  have h := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.mulVecLin B)) e
  have hcomp : (LinearMap.range (Matrix.mulVecLin B)).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((e : (Fin m → ℤ) →+ _)) = Matrix.mulVecLin B := by
    ext x : 1
    rfl
  have hd : LinearMap.det (Matrix.mulVecLin B) = B.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  have hcard : Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detAbs B := by
    rw [← h]
    unfold detAbs
    rw [hcomp, hd]
  have hfin : Finite ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    unfold detAbs
    exact Int.natAbs_ne_zero.mpr hdet
  have eq : FactorGroup B ≃ ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) :=
    (QuotientAddGroup.quotientAddEquivOfEq (lattice_eq_range B)).toEquiv
  exact ⟨Finite.of_equiv _ eq.symm, by rw [Nat.card_congr eq]; exact hcard⟩




theorem euclNorm_smul' {m : ℕ} (s : ℝ) (v : Fin m → ℝ) : euclNorm (s • v) = |s| * euclNorm v := by
  unfold euclNorm
  have : ∑ k, (s • v) k ^ 2 = s ^ 2 * ∑ k, v k ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; simp [mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

theorem euclNorm_pos' {m : ℕ} (v : Fin m → ℝ) (hv : v ≠ 0) : 0 < euclNorm v := by
  unfold euclNorm
  apply Real.sqrt_pos.2
  by_contra h
  apply hv
  have h0 : ∑ k, v k ^ 2 = 0 := le_antisymm (not_lt.1 h) (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  funext k
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (v k))).1 h0 k (Finset.mem_univ k)
  simpa using this

theorem basisCone_closed {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) : IsClosed (basisCone B) := by
  have : basisCone B = ⋂ k, {y : Fin m → ℝ | 0 ≤ ((realMatrix B)⁻¹ *ᵥ y) k} := by
    ext y; simp [basisCone]
  rw [this]
  apply isClosed_iInter
  intro k
  apply isClosed_le continuous_const
  have : Continuous (fun y : Fin m → ℝ => (realMatrix B)⁻¹ *ᵥ y) := by
    exact (Matrix.mulVecLin (realMatrix B)⁻¹).continuous_of_finiteDimensional
  exact (continuous_apply k).comp this

theorem sub_mem_core {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0)
    (d : ℝ) (y v : Fin m → ℝ) (hy : y ∈ deepCone B d) (hv : euclNorm v ≤ d) :
    y - v ∈ basisCone B := by
  by_contra hnot
  have hK := basisCone_closed B
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hnot (by simpa using hy.1)
  have hg : Continuous (fun s : ℝ => y - s • v) := by fun_prop
  let S : Set ℝ := {s | s ∈ Set.Icc (0:ℝ) 1 ∧ y - s • v ∈ basisCone B}
  have hSc : IsClosed S := by
    have : S = Set.Icc (0:ℝ) 1 ∩ (fun s : ℝ => y - s • v) ⁻¹' basisCone B := rfl
    rw [this]; exact isClosed_Icc.inter (hK.preimage hg)
  have hS0 : (0:ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, by simpa using hy.1⟩
  have hSb : BddAbove S := ⟨1, fun s hs => hs.1.2⟩
  have hmem : sSup S ∈ S := hSc.csSup_mem ⟨0, hS0⟩ hSb
  set s0 := sSup S with hs0
  have hs0le : ∀ s ∈ S, s ≤ s0 := fun s hs => le_csSup hSb hs
  have hs1 : s0 < 1 := by
    rcases lt_or_eq_of_le hmem.1.2 with h | h
    · exact h
    · exfalso; apply hnot; have := hmem.2; rw [h] at this; simpa using this
  have hz : y - s0 • v ∈ frontier (basisCone B) := by
    rw [frontier, hK.closure_eq]
    refine ⟨hmem.2, ?_⟩
    intro hint
    have hnhds : basisCone B ∈ nhds (y - s0 • v) := mem_interior_iff_mem_nhds.1 hint
    have := hg.continuousAt (x := s0) |>.preimage_mem_nhds hnhds
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 this
    have hs' : min (s0 + ε / 2) 1 ∈ S := by
      refine ⟨⟨le_min (by linarith [hmem.1.1]) zero_le_one, min_le_right _ _⟩, ?_⟩
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have : s0 < min (s0 + ε / 2) 1 := lt_min (by linarith) hs1
      rw [abs_of_pos (by linarith)]
      linarith [min_le_left (s0 + ε / 2) 1]
    have := hs0le _ hs'
    have : s0 < min (s0 + ε / 2) 1 := lt_min (by linarith) hs1
    linarith
  have hd := hy.2 _ hz
  have : y - (y - s0 • v) = s0 • v := by abel
  rw [this, euclNorm_smul', abs_of_nonneg hmem.1.1] at hd
  have hp := euclNorm_pos' v hv0
  nlinarith


open Matrix


open Matrix



variable {m n : ℕ}

theorem zero_of_not_mem_colSet (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (i : Fin n) (h : groupColumn B N i ∉ groupColumnSet B N) : groupColumn B N i = 0 := by
  classical
  by_contra h0
  apply h
  unfold groupColumnSet
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, h0⟩

theorem mem_colSet_of_ne (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (i : Fin n) (h : groupColumn B N i ≠ 0) : groupColumn B N i ∈ groupColumnSet B N := by
  by_contra h'
  exact h (zero_of_not_mem_colSet B N i h')

theorem zero_not_mem_colSet (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) :
    (0 : FactorGroup B) ∉ groupColumnSet B N := by
  classical
  unfold groupColumnSet
  simp

theorem mem_columnsOf (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (g : FactorGroup B) (i : Fin n) : i ∈ columnsOf B N g ↔ groupColumn B N i = g := by
  classical
  unfold columnsOf; simp

theorem fiber_total {α : Type*} [AddCommMonoid α] (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (F : Fin n → α) (hF : ∀ i, groupColumn B N i = 0 → F i = 0) :
    ∑ i, F i = ∑ g : ↥(groupColumnSet B N), ∑ i ∈ columnsOf B N (g : FactorGroup B), F i := by
  classical
  rw [Finset.sum_coe_sort (groupColumnSet B N) (fun g => ∑ i ∈ columnsOf B N g, F i)]
  have h1 : ∑ g ∈ groupColumnSet B N, ∑ i ∈ columnsOf B N g, F i
      = ∑ i ∈ Finset.univ.filter (fun i => groupColumn B N i ∈ groupColumnSet B N), F i := by
    have := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter
      (fun i => groupColumn B N i ∈ groupColumnSet B N)) (t := groupColumnSet B N)
      (g := groupColumn B N) (f := F) (fun i hi => (Finset.mem_filter.1 hi).2)
    rw [← this]
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sum_congr
    · ext i
      simp only [columnsOf, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨by rw [h]; exact hg, h⟩
      · intro h; exact h.2
    · intros; rfl
  rw [h1]
  symm
  apply Finset.sum_filter_of_ne
  intro i _ hne
  by_contra hn
  exact hne (hF i (zero_of_not_mem_colSet B N i hn))

theorem group_sum_eq (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (w : Fin n → ℕ) :
    ∑ i, w i • groupColumn B N i
      = ∑ g : ↥(groupColumnSet B N), (∑ i ∈ columnsOf B N (g : FactorGroup B), w i) • (g : FactorGroup B) := by
  rw [fiber_total B N (fun i => w i • groupColumn B N i) (fun i h => by simp [h])]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(mem_columnsOf B N _ i).1 hi]

theorem toGroup_Nmul (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (w : Fin n → ℕ) :
    toGroup B (fun k => ∑ i, N k i * (w i : ℤ)) = ∑ i, w i • groupColumn B N i := by
  have : (fun k => ∑ i, N k i * (w i : ℤ)) = ∑ i, w i • (fun k => N k i) := by
    funext k; simp [Finset.sum_apply, mul_comm]
  rw [this, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_nsmul]; rfl

theorem realMatrix_det (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) :
    (realMatrix B).det ≠ 0 := by
  have : (realMatrix B).det = (B.det : ℝ) := (RingHom.map_det (Int.castRingHom ℝ) B).symm
  rw [this]; exact_mod_cast hdet

theorem inv_cast (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) (z u : Fin m → ℤ)
    (h : B *ᵥ z = u) : (realMatrix B)⁻¹ *ᵥ realVec u = realVec z := by
  have hu : realVec u = realMatrix B *ᵥ realVec z := by
    funext k
    rw [← h]
    simp [Matrix.mulVec, dotProduct, realMatrix, realVec]
  rw [hu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (realMatrix_det B hdet)),
    Matrix.one_mulVec]


theorem toGroup_eq_of (B : Matrix (Fin m) (Fin m) ℤ) (a a' : Fin m → ℤ) (z : Fin m → ℤ)
    (h : B *ᵥ z = a - a') : toGroup B a = toGroup B a' := by
  have : a - a' ∈ basisLattice B := by
    rw [lattice_eq_range]; exact ⟨z, h⟩
  exact (QuotientAddGroup.eq_iff_sub_mem).2 this

theorem exists_z_of_group_eq (B : Matrix (Fin m) (Fin m) ℤ) (a a' : Fin m → ℤ)
    (h : toGroup B a = toGroup B a') : ∃ z : Fin m → ℤ, B *ᵥ z = a - a' := by
  have : a - a' ∈ basisLattice B := (QuotientAddGroup.eq_iff_sub_mem).1 h
  rw [lattice_eq_range] at this
  exact this

theorem basic_eq (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hdet : B.det ≠ 0) (xN : Fin n → ℕ) (z : Fin m → ℤ)
    (hz : B *ᵥ z = fun k => b k - ∑ i, N k i * (xN i : ℤ)) :
    ∀ k, (z k : ℝ) = basicPart B N b xN k := by
  intro k
  have := inv_cast B hdet z _ hz
  have h2 : basicPart B N b xN = (realMatrix B)⁻¹ *ᵥ realVec (fun k => b k - ∑ i, N k i * (xN i : ℤ)) := by
    unfold basicPart realVec
    congr 1
    funext k; push_cast; rfl
  rw [h2, this]; rfl

theorem alg_id (c1 : Fin m → ℝ) (c2 : Fin n → ℝ) (u : Fin m → ℝ) (P : Matrix (Fin m) (Fin n) ℝ)
    (xr : Fin n → ℝ) :
    ∑ k, c1 k * (u k - (P *ᵥ xr) k) + ∑ i, c2 i * xr i
      = ∑ k, c1 k * u k - ∑ i, (-c2 i + ∑ k, c1 k * P k i) * xr i := by
  simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, add_mul, neg_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  have h : ∑ x, ∑ i, c1 i * P i x * xr x = ∑ x, ∑ i, c1 x * (P x i * xr i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
  rw [h]
  ring

theorem objective_eq (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin m ⊕ Fin n → ℝ) (hdet : B.det ≠ 0) (x : Fin m ⊕ Fin n → ℤ)
    (hx : fullMatrix B N *ᵥ x = b) :
    objective c x = ∑ k, c (Sum.inl k) * ((realMatrix B)⁻¹ *ᵥ realVec b) k
      - ∑ i, relativePrice B N c i * (x (Sum.inr i) : ℝ) := by
  have hx' : B *ᵥ (x ∘ Sum.inl) = fun k => b k - ∑ i, N k i * x (Sum.inr i) := by
    have := hx
    unfold fullMatrix at this
    rw [Matrix.fromCols_mulVec] at this
    funext k
    have h := congrFun this k
    simp only [Pi.add_apply] at h
    simp only [Matrix.mulVec, dotProduct, Function.comp_apply] at h ⊢
    linarith
  have hb := inv_cast B hdet _ _ hx'
  have hM : (realMatrix B)⁻¹ *ᵥ realVec (fun k => b k - ∑ i, N k i * x (Sum.inr i))
      = (realMatrix B)⁻¹ *ᵥ realVec b
        - ((realMatrix B)⁻¹ * N.map (fun z : ℤ => (z : ℝ))) *ᵥ (fun i => (x (Sum.inr i) : ℝ)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub]
    congr 1
    funext k
    simp [realVec, Matrix.mulVec, dotProduct]
  rw [hM] at hb
  unfold objective
  rw [Fintype.sum_sum_type]
  have hB : ∀ k, (x (Sum.inl k) : ℝ) = ((realMatrix B)⁻¹ *ᵥ realVec b) k
      - (((realMatrix B)⁻¹ * N.map (fun z : ℤ => (z : ℝ))) *ᵥ (fun i => (x (Sum.inr i) : ℝ))) k := by
    intro k
    have := congrFun hb k
    simp only [realVec, Pi.sub_apply, Function.comp_apply] at this
    linarith
  rw [Finset.sum_congr rfl (fun k _ => by rw [hB k])]
  exact alg_id (fun k => c (Sum.inl k)) (fun i => c (Sum.inr i)) _ _ _


theorem vertex_t (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hdet : B.det ≠ 0)
    (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    ∃ t : ↥(groupColumnSet B N) → ℕ, t ∈ groupSolutions (groupColumnSet B N) (toGroup B b) ∧
      IsIrreducible (groupColumnSet B N) t ∧ toReal _ t = tstar ∧
      ∀ g : ↥(groupColumnSet B N), ∑ i ∈ columnsOf B N (g : FactorGroup B), xN i = t g := by
  haveI := (card_factor_core B hdet).1
  obtain ⟨t, hts, htr, hirr⟩ := thm2_core _ (zero_not_mem_colSet B N) _ tstar ht
  refine ⟨t, hts, hirr, htr, fun g => ?_⟩
  have := hx.1 g
  rw [← htr] at this
  simp only [toReal] at this
  exact_mod_cast this

theorem lift_group_eq (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (t : ↥(groupColumnSet B N) → ℕ) (ht : t ∈ groupSolutions (groupColumnSet B N) (toGroup B b))
    (xN : Fin n → ℕ) (h : ∀ g : ↥(groupColumnSet B N), ∑ i ∈ columnsOf B N (g : FactorGroup B), xN i = t g) :
    toGroup B (fun k => ∑ i, N k i * (xN i : ℤ)) = toGroup B b := by
  rw [toGroup_Nmul, group_sum_eq]
  simp only [h]
  exact ht

theorem cost_le (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (c : Fin m ⊕ Fin n → ℝ) (g : ↥(groupColumnSet B N)) (i : Fin n)
    (hi : i ∈ columnsOf B N (g : FactorGroup B)) : groupCost B N c g ≤ relativePrice B N c i :=
  Finset.inf'_le _ hi

theorem cost_eq (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (c : Fin m ⊕ Fin n → ℝ) (g : ↥(groupColumnSet B N)) (i : Fin n)
    (hi : i ∈ columnsOf B N (g : FactorGroup B))
    (hmin : ∀ j, groupColumn B N j = groupColumn B N i → relativePrice B N c i ≤ relativePrice B N c j) :
    relativePrice B N c i = groupCost B N c g := by
  apply le_antisymm
  · unfold groupCost
    apply Finset.le_inf'
    intro j hj
    exact hmin j (by rw [(mem_columnsOf B N _ j).1 hj, (mem_columnsOf B N _ i).1 hi])
  · exact cost_le B N c g i hi

theorem thm3_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN)
    (hnonneg : ∀ k, 0 ≤ basicPart B N b xN k) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) := by
  classical
  obtain ⟨t, hts, hirr, htr, hsum⟩ := vertex_t B N b hdet tstar ht.1 xN hx.1
  have hge := lift_group_eq B N b t hts xN hsum
  obtain ⟨z, hz⟩ := exists_z_of_group_eq B _ _ hge.symm
  have hzr := basic_eq B N b hdet xN z hz
  refine ⟨z, hzr, ?_⟩
  have hfeas : IsFeasible B N b (Sum.elim z (fun i => (xN i : ℤ))) := by
    refine ⟨?_, ?_⟩
    · rintro (k | i)
      · have := hnonneg k
        rw [← hzr k] at this
        simpa using (by exact_mod_cast this : (0:ℤ) ≤ z k)
      · simp
    · unfold fullMatrix
      rw [Matrix.fromCols_mulVec_sumElim, hz]
      funext k
      simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨hfeas, ?_⟩
  intro y hy
  have hyb := hy.2
  have hxb := hfeas.2
  rw [objective_eq B N b c hdet y hyb, objective_eq B N b c hdet _ hxb]
  simp only [Sum.elim_inr]
  suffices h : ∑ i, relativePrice B N c i * ((xN i : ℤ) : ℝ) ≤
      ∑ i, relativePrice B N c i * (y (Sum.inr i) : ℝ) by linarith
  -- y data
  have hy0 : ∀ i, 0 ≤ y (Sum.inr i) := fun i => hy.1 _
  let yN : Fin n → ℕ := fun i => (y (Sum.inr i)).toNat
  have hyN : ∀ i, (yN i : ℤ) = y (Sum.inr i) := fun i => Int.toNat_of_nonneg (hy0 i)
  have hyN' : ∀ i, (yN i : ℝ) = (y (Sum.inr i) : ℝ) := fun i => by exact_mod_cast hyN i
  have hyeq : B *ᵥ (y ∘ Sum.inl) = fun k => b k - ∑ i, N k i * (yN i : ℤ) := by
    have := hyb
    unfold fullMatrix at this
    rw [Matrix.fromCols_mulVec] at this
    funext k
    have h := congrFun this k
    simp only [Pi.add_apply] at h
    simp only [Matrix.mulVec, dotProduct, Function.comp_apply, hyN] at h ⊢
    linarith
  have hgy : toGroup B (fun k => ∑ i, N k i * (yN i : ℤ)) = toGroup B b :=
    (toGroup_eq_of B _ _ (y ∘ Sum.inl) (by rw [hyeq]; funext k; simp)).symm
  let s : ↥(groupColumnSet B N) → ℕ := fun g => ∑ i ∈ columnsOf B N (g : FactorGroup B), yN i
  have hs : s ∈ groupSolutions (groupColumnSet B N) (toGroup B b) := by
    unfold groupSolutions
    show ∑ g : ↥(groupColumnSet B N), s g • (g : FactorGroup B) = toGroup B b
    rw [← group_sum_eq B N yN, ← toGroup_Nmul]; exact hgy
  have hmin := ht.2 s hs
  rw [← htr] at hmin
  simp only [toReal] at hmin
  -- LHS equality
  have hL : ∑ i, relativePrice B N c i * ((xN i : ℤ) : ℝ)
      = ∑ g : ↥(groupColumnSet B N), groupCost B N c g * (t g : ℝ) := by
    rw [fiber_total B N (fun i => relativePrice B N c i * ((xN i : ℤ) : ℝ))
      (fun i h => by simp [hx.1.2.2 i h])]
    apply Finset.sum_congr rfl
    intro g _
    have : ∀ i ∈ columnsOf B N (g : FactorGroup B),
        relativePrice B N c i * ((xN i : ℤ) : ℝ) = groupCost B N c g * (xN i : ℝ) := by
      intro i hi
      simp only [Int.cast_natCast]
      rcases Nat.eq_zero_or_pos (xN i) with h0 | hpos
      · simp [h0]
      · rw [cost_eq B N c g i hi (hx.2 i hpos)]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← Nat.cast_sum, hsum g]
  -- RHS bound
  have hR : ∑ g : ↥(groupColumnSet B N), groupCost B N c g * (s g : ℝ)
      ≤ ∑ i, relativePrice B N c i * (y (Sum.inr i) : ℝ) := by
    let F : Fin n → ℝ := fun i =>
      (if groupColumn B N i = 0 then 0 else relativePrice B N c i) * (yN i : ℝ)
    have h1 : ∑ i, F i ≤ ∑ i, relativePrice B N c i * (y (Sum.inr i) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← hyN' i]
      simp only [F]
      split_ifs
      · rw [zero_mul]; exact mul_nonneg (hopt.2 i) (Nat.cast_nonneg _)
      · exact le_rfl
    refine le_trans ?_ h1
    rw [fiber_total B N F (fun i h => by simp [F, h])]
    apply Finset.sum_le_sum
    intro g _
    have : ∀ i ∈ columnsOf B N (g : FactorGroup B), groupCost B N c g * (yN i : ℝ) ≤ F i := by
      intro i hi
      have hg := (mem_columnsOf B N _ i).1 hi
      have hne : groupColumn B N i ≠ 0 := by
        rw [hg]; intro h0
        exact zero_not_mem_colSet B N (h0 ▸ g.2)
      simp only [F, if_neg hne]
      exact mul_le_mul_of_nonneg_right (cost_le B N c g i hi) (Nat.cast_nonneg _)
    calc groupCost B N c g * (s g : ℝ)
        = ∑ i ∈ columnsOf B N (g : FactorGroup B), groupCost B N c g * (yN i : ℝ) := by
          simp only [s, Nat.cast_sum, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum this
  rw [hL]
  exact le_trans hmin hR


theorem euclNorm_add_le (u v : Fin m → ℝ) : euclNorm (u + v) ≤ euclNorm u + euclNorm v := by
  have h : ∀ w : Fin m → ℝ, euclNorm w = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin m))‖ := by
    intro w
    rw [EuclideanSpace.norm_eq]
    simp [euclNorm]
  rw [h, h, h]
  have : (WithLp.toLp 2 (u + v) : EuclideanSpace ℝ (Fin m)) = WithLp.toLp 2 u + WithLp.toLp 2 v := rfl
  rw [this]
  exact norm_add_le _ _

theorem euclNorm_zero' : euclNorm (0 : Fin m → ℝ) = 0 := by simp [euclNorm]

theorem euclNorm_nonneg' (v : Fin m → ℝ) : 0 ≤ euclNorm v := Real.sqrt_nonneg _

theorem euclNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin m → ℝ) :
    euclNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, euclNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euclNorm_zero']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (euclNorm_add_le _ _) (add_le_add_right ih _)

theorem col_le_lmax (N : Matrix (Fin m) (Fin n) ℤ) (i : Fin n) :
    euclNorm (fun k => (N k i : ℝ)) ≤ lmax N :=
  le_ciSup (f := fun i : Fin n => euclNorm (fun k => (N k i : ℝ))) (Set.finite_range _).bddAbove i

theorem lmax_nonneg (N : Matrix (Fin m) (Fin n) ℤ) : 0 ≤ lmax N :=
  Real.iSup_nonneg (fun i => euclNorm_nonneg' _)

theorem card_eq_detAbs (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) [Fintype (FactorGroup B)] :
    Fintype.card (FactorGroup B) = detAbs B := by
  rw [← Nat.card_eq_fintype_card]; exact (card_factor_core B hdet).2

theorem detAbs_pos (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) : 1 ≤ detAbs B := by
  unfold detAbs; exact Int.natAbs_pos.2 hdet

theorem sum_xN_le (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hdet : B.det ≠ 0) (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    ∑ i, xN i ≤ detAbs B - 1 := by
  classical
  obtain ⟨t, hts, hirr, htr, hsum⟩ := vertex_t B N b hdet tstar ht xN hx
  haveI := (card_factor_core B hdet).1
  letI := Fintype.ofFinite (FactorGroup B)
  have h1 := sum_le_core _ (zero_not_mem_colSet B N) t hirr
  rw [card_eq_detAbs B hdet] at h1
  have h2 : ∑ i, xN i = ∑ g : ↥(groupColumnSet B N), t g := by
    rw [fiber_total B N xN (fun i h => hx.2.2 i h)]
    exact Finset.sum_congr rfl (fun g _ => hsum g)
  omega

theorem norm_le_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (hdet : B.det ≠ 0) (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    euclNorm (fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) ≤ lmax N * ((detAbs B : ℝ) - 1) := by
  have hs := sum_xN_le B N b hdet tstar ht xN hx
  have hpos := detAbs_pos B hdet
  have hs' : (∑ i, (xN i : ℝ)) ≤ (detAbs B : ℝ) - 1 := by
    have : ((∑ i, xN i : ℕ) : ℝ) ≤ ((detAbs B - 1 : ℕ) : ℝ) := by exact_mod_cast hs
    rw [Nat.cast_sub hpos] at this
    simpa using this
  have hv : (fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) = ∑ i, (xN i : ℝ) • (fun k => (N k i : ℝ)) := by
    funext k; simp [Finset.sum_apply, mul_comm]
  rw [hv]
  refine le_trans (euclNorm_sum_le _ _) ?_
  calc ∑ i, euclNorm ((xN i : ℝ) • fun k => (N k i : ℝ))
      = ∑ i, (xN i : ℝ) * euclNorm (fun k => (N k i : ℝ)) := by
        apply Finset.sum_congr rfl; intro i _
        rw [euclNorm_smul', abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ i, (xN i : ℝ) * lmax N := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (col_le_lmax N i) (Nat.cast_nonneg _)
    _ = (∑ i, (xN i : ℝ)) * lmax N := by rw [Finset.sum_mul]
    _ ≤ ((detAbs B : ℝ) - 1) * lmax N := mul_le_mul_of_nonneg_right hs' (lmax_nonneg N)
    _ = _ := by ring

theorem nonneg_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (hdet : B.det ≠ 0)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    ∀ k, 0 ≤ basicPart B N b xN k := by
  have hn := norm_le_core B N b hdet tstar ht xN hx
  have hmem := sub_mem_core B hdet _ (realVec b) (fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) hb hn
  intro k
  have := hmem k
  have e : basicPart B N b xN = (realMatrix B)⁻¹ *ᵥ (realVec b - fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) := by
    unfold basicPart realVec; rfl
  rw [e]; exact this

theorem thm4_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) :=
  thm3_core B N b c hunit hdet hopt tstar ht xN hx (nonneg_core B N b hdet hb tstar ht.1 xN hx.1)


theorem fiber_prod {α : Type*} [CommMonoid α] (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (F : Fin n → α) (hF : ∀ i, groupColumn B N i = 0 → F i = 1) :
    ∏ i, F i = ∏ g : ↥(groupColumnSet B N), ∏ i ∈ columnsOf B N (g : FactorGroup B), F i := by
  classical
  rw [Finset.prod_coe_sort (groupColumnSet B N) (fun g => ∏ i ∈ columnsOf B N g, F i)]
  have h1 : ∏ g ∈ groupColumnSet B N, ∏ i ∈ columnsOf B N g, F i
      = ∏ i ∈ Finset.univ.filter (fun i => groupColumn B N i ∈ groupColumnSet B N), F i := by
    have := Finset.prod_fiberwise_of_maps_to (s := Finset.univ.filter
      (fun i => groupColumn B N i ∈ groupColumnSet B N)) (t := groupColumnSet B N)
      (g := groupColumn B N) (f := F) (fun i hi => (Finset.mem_filter.1 hi).2)
    rw [← this]
    apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr
    · ext i
      simp only [columnsOf, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨by rw [h]; exact hg, h⟩
      · intro h; exact h.2
    · intros; rfl
  rw [h1]
  symm
  apply Finset.prod_filter_of_ne
  intro i _ hne
  by_contra hn
  exact hne (hF i (zero_of_not_mem_colSet B N i hn))

theorem prod_one_add_sum (s : Finset (Fin n)) (xN : Fin n → ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → xN i = 0 ∨ xN j = 0) :
    ∏ i ∈ s, (1 + xN i) = 1 + ∑ i ∈ s, xN i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → xN i = 0 ∨ xN j = 0 :=
      fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    rw [ih hs]
    by_cases h0 : xN a = 0
    · simp [h0]
    · have : ∑ i ∈ s, xN i = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rcases h a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact ha hj) with h1 | h1
        · exact absurd h1 h0
        · exact h1
      rw [this]; simp

theorem prod_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (hdet : B.det ≠ 0) (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    ∏ i, (1 + xN i) ≤ detAbs B := by
  classical
  obtain ⟨t, hts, hirr, htr, hsum⟩ := vertex_t B N b hdet tstar ht xN hx
  haveI := (card_factor_core B hdet).1
  letI := Fintype.ofFinite (FactorGroup B)
  have h1 := thm1_core _ (zero_not_mem_colSet B N) t hirr
  rw [card_eq_detAbs B hdet] at h1
  have h2 : ∏ i, (1 + xN i) = ∏ g : ↥(groupColumnSet B N), (1 + t g) := by
    rw [fiber_prod B N (fun i => 1 + xN i) (fun i h => by simp [hx.2.2 i h])]
    apply Finset.prod_congr rfl
    intro g _
    rw [prod_one_add_sum _ xN, hsum g]
    intro i hi j hj hij
    exact hx.2.1 i j hij (by rw [(mem_columnsOf B N _ i).1 hi, (mem_columnsOf B N _ j).1 hj])
  rw [h2]; exact h1

theorem display10_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) ∧
      ∏ i : Fin n, (1 + xN i) ≤ detAbs B := by
  obtain ⟨xB, h1, h2⟩ := thm4_core B N b c hunit hdet hopt hb tstar ht xN hx
  exact ⟨xB, h1, h2, prod_core B N b hdet tstar ht.1 xN hx.1⟩


end Gomory69.Asymptotic

open Gomory69.Asymptotic


theorem solution {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN)
    (hnonneg : ∀ k, 0 ≤ basicPart B N b xN k) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) := by
  exact thm3_core B N b c hunit hdet hopt tstar ht xN hx hnonneg
