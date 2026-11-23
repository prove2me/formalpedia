-- Prove2me | solution 1 for LogConcaveLattice.Lift.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:31:29.833348+00:00
-- url     : https://prove2.me/submissions/232e544d-8218-4a90-910c-dedf742d70b1

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Theorems.Thm_LogConcaveLattice_Lift_lemma_2_2

open scoped RealInnerProductSpace Matrix
open MeasureTheory LogConcaveLattice.Lift

namespace AuxLemma23

lemma starProj_mem {n : ℕ} (E : Submodule ℝ (V n)) (x : V n) :
    E.starProjection x ∈ E :=
  (E.orthogonalProjectionOnto x).2

lemma starProj_eq_zero_iff {n : ℕ} (E : Submodule ℝ (V n)) (x : V n) :
    E.starProjection x = 0 ↔ x ∈ Eᗮ := by
  have hdecomp := E.starProjection_add_starProjection_orthogonal x
  constructor
  · intro h0
    rw [h0, zero_add] at hdecomp
    rw [← hdecomp]
    exact starProj_mem Eᗮ x
  · intro hx
    have hself : Eᗮ.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    rw [hself] at hdecomp
    simpa using hdecomp

lemma inner_starProj_right_of_mem {n : ℕ} (E : Submodule ℝ (V n)) {x : V n} (hx : x ∈ E) (y : V n) :
    ⟪x, E.starProjection y⟫ = ⟪x, y⟫ := by
  have hdecomp := (E.starProjection_add_starProjection_orthogonal y).symm
  have horth : ⟪x, Eᗮ.starProjection y⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' E (Eᗮ.starProjection y)).mp (starProj_mem Eᗮ y) x hx
  conv_rhs => rw [hdecomp]
  rw [inner_add_right, horth, add_zero]

lemma mem_span_range_exists_fun {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Fintype ι] [DecidableEq ι] {v : ι → M} {x : M} (hx : x ∈ Submodule.span R (Set.range v)) :
    ∃ c : ι → R, ∑ i, c i • v i = x := by
  refine Submodule.span_induction (p := fun y _ => ∃ c : ι → R, ∑ i, c i • v i = y) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  · exact ⟨0, by simp⟩
  · rintro y₁ y₂ _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
    exact ⟨c₁ + c₂, by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  · rintro r y _ ⟨c, rfl⟩
    exact ⟨fun i => r * c i, by simp [mul_smul, Finset.smul_sum]⟩

lemma span_int_subset_span_real {n : ℕ} (s : Set (V n)) :
    (Submodule.span ℤ s : Set (V n)) ⊆ (Submodule.span ℝ s : Set (V n)) := by
  intro x hx
  refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span ℝ s) ?_ ?_ ?_ ?_ hx
  · intro y hy; exact Submodule.subset_span hy
  · exact Submodule.zero_mem _
  · intro y₁ y₂ _ _ h₁ h₂; exact Submodule.add_mem _ h₁ h₂
  · intro z y _ hy
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ hy

lemma span_projLattice {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (F : Submodule ℝ (V n)) :
    Submodule.span ℝ (projLattice F Λ : Set (V n)) = F := by
  have hset : (projLattice F Λ : Set (V n)) =
      (F.starProjection : V n →ₗ[ℝ] V n) '' (Λ : Set (V n)) := rfl
  rw [hset, ← LinearMap.map_span, IsZLattice.span_top]
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact starProj_mem F y
  · intro hx
    exact ⟨x, trivial, Submodule.starProjection_eq_self_iff.mpr hx⟩

lemma dual_projLattice {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (E : Submodule ℝ (V n)) :
    dual (projLattice Eᗮ Λ) = interSubspace (dual Λ) Eᗮ := by
  ext x
  have hspan_proj := span_projLattice Λ Eᗮ
  have hspan_top : Submodule.span ℝ (Λ : Set (V n)) = ⊤ := IsZLattice.span_top
  change (x ∈ Submodule.span ℝ (projLattice Eᗮ Λ : Set (V n)) ∧
      ∀ γ ∈ projLattice Eᗮ Λ, ∃ m : ℤ, ⟪x, γ⟫ = m) ↔
    ((x ∈ Submodule.span ℝ (Λ : Set (V n)) ∧ ∀ l ∈ Λ, ∃ m : ℤ, ⟪x, l⟫ = m) ∧ x ∈ Eᗮ)
  rw [hspan_proj, hspan_top]
  constructor
  · rintro ⟨hxE, hγ⟩
    refine ⟨⟨trivial, fun l hl => ?_⟩, hxE⟩
    obtain ⟨m, hm⟩ := hγ (Eᗮ.starProjection l) ⟨l, hl, rfl⟩
    have heq : ⟪x, Eᗮ.starProjection l⟫ = ⟪x, l⟫ := inner_starProj_right_of_mem Eᗮ hxE l
    exact ⟨m, heq ▸ hm⟩
  · rintro ⟨⟨_, hl⟩, hxE⟩
    refine ⟨hxE, ?_⟩
    rintro γ ⟨l, hlΛ, rfl⟩
    obtain ⟨m, hm⟩ := hl l hlΛ
    have heq : ⟪x, Eᗮ.starProjection l⟫ = ⟪x, l⟫ := inner_starProj_right_of_mem Eᗮ hxE l
    exact ⟨m, heq.symm ▸ hm⟩

lemma discrete_sublattice {n : ℕ} {Λ : Submodule ℤ (V n)} [DiscreteTopology Λ]
    (Γ : Submodule ℤ (V n)) (hΓ : Γ ≤ Λ) : DiscreteTopology Γ := by
  have hopen : IsOpen ({0} : Set Λ) :=
    discreteTopology_iff_isOpen_singleton_zero.mp inferInstance
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen 0 (Set.mem_singleton 0)
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have hy' : (⟨(y : V n), hΓ y.2⟩ : Λ) ∈ Metric.ball (0 : Λ) δ := by
    simpa [Metric.mem_ball, Subtype.dist_eq] using hy
  have h0 : (⟨(y : V n), hΓ y.2⟩ : Λ) = 0 := Set.mem_singleton_iff.mp (hδ hy')
  exact Subtype.ext (congrArg (fun u : Λ => (u : V n)) h0)

lemma span_real_of_isLatticeBasis {n k : ℕ} {Γ : Submodule ℤ (V n)} {b : Fin k → V n}
    (hb : IsLatticeBasis Γ b) :
    Submodule.span ℝ (Set.range b) = Submodule.span ℝ (Γ : Set (V n)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    rw [← hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Submodule.span_le]
    intro x hx
    rw [← hb.2] at hx
    exact span_int_subset_span_real (Set.range b) hx

lemma exists_isLatticeBasis {n : ℕ} (Γ : Submodule ℤ (V n)) [DiscreteTopology Γ] :
    ∃ k : ℕ, ∃ b : Fin k → V n, IsLatticeBasis Γ b := by
  let W : Submodule ℝ (V n) := Submodule.span ℝ (Γ : Set (V n))
  let L₀ : Submodule ℤ W := Γ.comap (W.subtype.restrictScalars ℤ)
  have hL₀_disc : DiscreteTopology L₀ := by
    have hopen : IsOpen ({0} : Set Γ) :=
      discreteTopology_iff_isOpen_singleton_zero.mp inferInstance
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen 0 (Set.mem_singleton 0)
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    have hyΓ : ((y.1 : W) : V n) ∈ Γ := y.2
    have hy' : (⟨((y.1 : W) : V n), hyΓ⟩ : Γ) ∈ Metric.ball (0 : Γ) δ := by
      rw [Metric.mem_ball] at hy ⊢
      exact hy
    have h0 : (⟨((y.1 : W) : V n), hyΓ⟩ : Γ) = 0 := Set.mem_singleton_iff.mp (hδ hy')
    exact Subtype.ext (Subtype.ext (congrArg (fun u : Γ => (u : V n)) h0))
  have : DiscreteTopology L₀ := hL₀_disc
  have hL₀_lat : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, W.range_subtype]
    have hset : W.subtype '' (L₀ : Set W) = (Γ : Set (V n)) := by
      ext x
      constructor
      · rintro ⟨⟨y, hyW⟩, hyΓ, rfl⟩
        exact hyΓ
      · intro hx
        exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
    rw [hset]
  have : IsZLattice ℝ L₀ := hL₀_lat
  let b₀ := Module.Free.chooseBasis ℤ L₀
  let B₀ := b₀.ofZLatticeBasis ℝ L₀
  let k := Module.finrank ℝ W
  let e : Fin k ≃ Module.Free.ChooseBasisIndex ℤ L₀ :=
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B₀).symm).symm
  let b : Fin k → V n := fun i => ((b₀ (e i) : W) : V n)
  refine ⟨k, b, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgW : ∑ i : Fin k, g i • B₀ (e i) = 0 := by
      apply Subtype.ext
      simpa [AddSubmonoidClass.coe_finsetSum, b, B₀] using hg
    exact Fintype.linearIndependent_iff.mp (B₀.linearIndependent.comp e e.injective) g hgW
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (b₀ (e i)).2
    · intro x hx
      let x₀ : L₀ := ⟨⟨x, Submodule.subset_span hx⟩, hx⟩
      have hx₀ : x₀ = ∑ j, b₀.repr x₀ j • b₀ j := (b₀.sum_repr x₀).symm
      have hx_sum : x = ∑ i : Fin k, b₀.repr x₀ (e i) • b i := by
        have hval : ((x₀ : W) : V n) = ∑ j, b₀.repr x₀ j • ((b₀ j : W) : V n) := by
          have hW : (x₀ : W) = ∑ j, b₀.repr x₀ j • (b₀ j : W) := by
            conv_lhs => rw [hx₀]
            rw [AddSubmonoidClass.coe_finsetSum]
            rfl
          calc
            ((x₀ : W) : V n) = ((∑ j, b₀.repr x₀ j • (b₀ j : W) : W) : V n) := by rw [hW]
            _ = ∑ j, b₀.repr x₀ j • ((b₀ j : W) : V n) := by
              rw [AddSubmonoidClass.coe_finsetSum]
              rfl
        rw [← e.sum_comp (fun j => b₀.repr x₀ j • ((b₀ j : W) : V n))] at hval
        exact hval
      rw [hx_sum]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma gram_det_eq_of_same_card {n k : ℕ} {Γ : Submodule ℤ (V n)}
    {b b' : Fin k → V n} (hb : IsLatticeBasis Γ b) (hb' : IsLatticeBasis Γ b') :
    (Matrix.gram ℝ b).det = (Matrix.gram ℝ b').det := by
  have hmem : ∀ j : Fin k, ∃ u : Fin k → ℤ, ∑ i, u i • b' i = b j := by
    intro j
    apply mem_span_range_exists_fun
    rw [hb'.2, ← hb.2]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hmem' : ∀ j : Fin k, ∃ v : Fin k → ℤ, ∑ i, v i • b i = b' j := by
    intro j
    apply mem_span_range_exists_fun
    rw [hb.2, ← hb'.2]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose u hu using hmem
  choose v hv using hmem'
  let U : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => u j i
  let Vm : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => v j i
  have hb_exp : ∀ j : Fin k, b j = ∑ i : Fin k, (U i j : ℝ) • b' i := by
    intro j
    rw [← hu j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    rfl
  have hb'_exp : ∀ i : Fin k, b' i = ∑ l : Fin k, (Vm l i : ℝ) • b l := by
    intro i
    rw [← hv i]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    rfl
  have hVU : Vm * U = 1 := by
    ext l j
    have hlin := Fintype.linearIndependent_iff.mp hb.1
    have hexp : ∑ l : Fin k, (((Vm * U) l j : ℤ) : ℝ) • b l =
        ∑ l : Fin k, ((1 : Matrix (Fin k) (Fin k) ℤ) l j : ℝ) • b l := by
      calc
        ∑ l : Fin k, (((Vm * U) l j : ℤ) : ℝ) • b l
            = ∑ l : Fin k, (∑ i : Fin k, (Vm l i : ℝ) * (U i j : ℝ)) • b l := by
              refine Finset.sum_congr rfl fun l _ => ?_
              simp [Matrix.mul_apply]
        _ = ∑ i : Fin k, (U i j : ℝ) • ∑ l : Fin k, (Vm l i : ℝ) • b l := by
              simp_rw [Finset.sum_smul, mul_comm (Vm _ _ : ℝ) (U _ _ : ℝ), mul_smul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => by rw [Finset.smul_sum]
        _ = b j := by
              simp_rw [← hb'_exp]
              exact (hb_exp j).symm
        _ = ∑ l : Fin k, ((1 : Matrix (Fin k) (Fin k) ℤ) l j : ℝ) • b l := by
              simp [Matrix.one_apply]
    have hdiff : ∑ r : Fin k, ((((Vm * U) r j : ℤ) : ℝ) -
        ((1 : Matrix (Fin k) (Fin k) ℤ) r j : ℝ)) • b r = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib, hexp, sub_self]
    have hzero := hlin _ hdiff l
    have hreal : (((Vm * U) l j : ℤ) : ℝ) = ((1 : Matrix (Fin k) (Fin k) ℤ) l j : ℝ) :=
      sub_eq_zero.mp hzero
    exact Int.cast_injective hreal
  have hdet_unit : Vm.det * U.det = 1 := by
    rw [← Matrix.det_mul, hVU, Matrix.det_one]
  have hUdet_sq : ((U.det : ℤ) : ℝ) ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet_unit with ⟨_, hU1⟩ | ⟨_, hU1⟩
    · rw [hU1]; norm_num
    · rw [hU1]; norm_num
  let UR : Matrix (Fin k) (Fin k) ℝ := U.map (Int.cast : ℤ → ℝ)
  have hUR_det : UR.det = (U.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det U).symm
  have hgram : Matrix.gram ℝ b = URᵀ * Matrix.gram ℝ b' * UR := by
    ext i j
    simp only [Matrix.gram_apply, hb_exp, inner_sum, sum_inner, real_inner_smul_left,
      real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, UR, Matrix.map_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hUR_det]
  calc
    (U.det : ℝ) * (Matrix.gram ℝ b').det * (U.det : ℝ)
        = ((U.det : ℝ) ^ 2) * (Matrix.gram ℝ b').det := by ring
    _ = 1 * (Matrix.gram ℝ b').det := by rw [hUdet_sq]
    _ = (Matrix.gram ℝ b').det := one_mul _

lemma latticeDet_eq_of_isLatticeBasis {n k : ℕ} {Γ : Submodule ℤ (V n)} {b : Fin k → V n}
    (hb : IsLatticeBasis Γ b) :
    latticeDet Γ = Real.sqrt (Matrix.gram ℝ b).det := by
  have hex : ∃ k' : ℕ, ∃ b' : Fin k' → V n, IsLatticeBasis Γ b' := ⟨k, b, hb⟩
  simp only [latticeDet, dif_pos hex]
  let k' := hex.choose
  let b' := hex.choose_spec.choose
  have hb' : IsLatticeBasis Γ b' := hex.choose_spec.choose_spec
  have hspan_eq : Submodule.span ℝ (Set.range b) = Submodule.span ℝ (Set.range b') := by
    rw [span_real_of_isLatticeBasis hb, span_real_of_isLatticeBasis hb']
  have hk : k = k' := by
    have h1 := finrank_span_eq_card hb.1
    have h2 := finrank_span_eq_card hb'.1
    rw [hspan_eq, h2] at h1
    simpa using h1.symm
  subst hk
  rw [gram_det_eq_of_same_card hb hb']

lemma gram_posDef {n k : ℕ} {b : Fin k → V n} (hli : LinearIndependent ℝ b) :
    (Matrix.gram ℝ b).PosDef := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp [Matrix.gram_apply, real_inner_comm]
  · intro v hv
    have hsum_ne : ∑ i : Fin k, v i • b i ≠ 0 := by
      intro h0
      exact hv (Finsupp.ext (Fintype.linearIndependent_iff.mp hli (⇑v) h0))
    have hpos : 0 < ‖∑ i : Fin k, v i • b i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hsum_ne)
    have hquad : (v.sum fun i xi => v.sum fun j xj => star xi * Matrix.gram ℝ b i j * xj) =
        ‖∑ i : Fin k, v i • b i‖ ^ 2 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      have hinner : ∀ i : Fin k,
          (v.sum fun j xj => star (v i) * Matrix.gram ℝ b i j * xj) =
            ∑ j : Fin k, star (v i) * Matrix.gram ℝ b i j * v j :=
        fun i => Finsupp.sum_fintype _ _ (fun _ => by simp)
      simp_rw [hinner]
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, star_trivial,
        Matrix.gram_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => by ring
    rwa [hquad]

lemma gram_det_pos {n k : ℕ} {b : Fin k → V n} (hli : LinearIndependent ℝ b) :
    0 < (Matrix.gram ℝ b).det :=
  (gram_posDef hli).det_pos

lemma dual_latticeSubspace_of_proj {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (E : Submodule ℝ (V n)) (hE : IsLatticeSubspace Λ E) :
    IsLatticeSubspace (dual Λ) Eᗮ := by
  have hE_orth : IsLatticeSubspace Λ Eᗮᗮ := by
    rwa [Submodule.orthogonal_orthogonal]
  have hdisc : DiscreteTopology (projLattice Eᗮ Λ) :=
    (LogConcaveLattice.Lift.lemma_2_2 n Λ Eᗮ).mpr hE_orth
  have : DiscreteTopology (projLattice Eᗮ Λ) := hdisc
  obtain ⟨m, b, hb⟩ := exists_isLatticeBasis (projLattice Eᗮ Λ)
  let G := Matrix.gram ℝ b
  have hGpos : 0 < G.det := gram_det_pos hb.1
  have hGunit : IsUnit G.det := isUnit_iff_ne_zero.mpr (ne_of_gt hGpos)
  let b_dual : Fin m → V n := fun i => ∑ j : Fin m, G⁻¹ i j • b j
  have hspan_b : Submodule.span ℝ (Set.range b) = Eᗮ := by
    rw [span_real_of_isLatticeBasis hb, span_projLattice Λ Eᗮ]
  have hb_dual_mem : ∀ i : Fin m, b_dual i ∈ interSubspace (dual Λ) Eᗮ := by
    intro i
    rw [← dual_projLattice Λ E]
    refine ⟨?_, ?_⟩
    · rw [span_projLattice Λ Eᗮ, ← hspan_b]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro γ hγ
      rw [← hb.2] at hγ
      obtain ⟨z, rfl⟩ := mem_span_range_exists_fun hγ
      refine ⟨z i, ?_⟩
      have horth : ∀ k : Fin m, ⟪b_dual i, b k⟫ = if i = k then 1 else 0 := by
        intro k
        simp only [b_dual, sum_inner, real_inner_smul_left]
        have hmul : ∑ j : Fin m, G⁻¹ i j * ⟪b j, b k⟫ = (G⁻¹ * G) i k := by
          simp [Matrix.mul_apply, G, Matrix.gram_apply]
        rw [hmul, Matrix.nonsing_inv_mul G hGunit, Matrix.one_apply]
      calc
        ⟪b_dual i, ∑ k : Fin m, z k • b k⟫
            = ∑ k : Fin m, (z k : ℝ) * ⟪b_dual i, b k⟫ := by
              rw [inner_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
        _ = ∑ k : Fin m, (z k : ℝ) * (if i = k then 1 else 0) := by
              refine Finset.sum_congr rfl fun k _ => by rw [horth k]
        _ = (z i : ℝ) := by simp
  change Submodule.span ℝ (interSubspace (dual Λ) Eᗮ : Set (V n)) = Eᗮ
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · have hsub : Set.range b ⊆ (Submodule.span ℝ (interSubspace (dual Λ) Eᗮ : Set (V n)) : Set (V n)) := by
      rintro _ ⟨j, rfl⟩
      have hbj : b j = ∑ i : Fin m, G j i • b_dual i := by
        simp only [b_dual, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have hmul : ∀ k : Fin m, (∑ i : Fin m, G j i * G⁻¹ i k) = (G * G⁻¹) j k := by
          intro k; simp [Matrix.mul_apply]
        calc
          b j = ∑ k : Fin m, (1 : Matrix (Fin m) (Fin m) ℝ) j k • b k := by
            simp [Matrix.one_apply]
          _ = ∑ k : Fin m, (G * G⁻¹) j k • b k := by
            rw [Matrix.mul_nonsing_inv G hGunit]
          _ = ∑ k : Fin m, (∑ i : Fin m, G j i * G⁻¹ i k) • b k := by
            refine Finset.sum_congr rfl fun k _ => by rw [hmul k]
          _ = ∑ k : Fin m, ∑ i : Fin m, (G j i * G⁻¹ i k) • b k := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_smul
      rw [hbj]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (hb_dual_mem i))
    conv_lhs => rw [← hspan_b]
    rw [Submodule.span_le]
    exact hsub

lemma covolume_eq_latticeDet {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    ZLattice.covolume Λ = latticeDet Λ := by
  let eCLM : V n ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let eL : V n ≃ₗ[ℝ] (Fin n → ℝ) := eCLM.toLinearEquiv
  have hmp : MeasurePreserving eL volume volume := PiLp.volume_preserving_ofLp (Fin n)
  let L' : Submodule ℤ (Fin n → ℝ) := Λ.map (eL.toLinearMap.restrictScalars ℤ)
  have hL'_disc : DiscreteTopology L' := by
    let f : L' → Λ := fun y =>
      ⟨eL.symm y.1, by
        obtain ⟨x, hx, hxy⟩ := y.2
        have hx_eq : eL x = y.1 := hxy
        rw [← hx_eq, eL.symm_apply_apply]
        exact hx⟩
    have hf_cont : Continuous f := by
      apply Continuous.subtype_mk
      exact eCLM.symm.continuous.comp continuous_subtype_val
    have hf_inj : Function.Injective f := by
      intro a b hab
      have : eL.symm a.1 = eL.symm b.1 := congrArg Subtype.val hab
      exact Subtype.ext (eL.symm.injective this)
    have hopen : IsOpen ({0} : Set Λ) :=
      discreteTopology_iff_isOpen_singleton_zero.mp inferInstance
    rw [discreteTopology_iff_isOpen_singleton_zero]
    convert hopen.preimage hf_cont using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro hy; subst hy; ext; simp [f]
    · intro hfy
      have : f y = f 0 := by rw [hfy]; ext; simp [f]
      exact hf_inj this
  have : DiscreteTopology L' := hL'_disc
  have hL'_lat : IsZLattice ℝ L' := by
    refine ⟨?_⟩
    have hset : (L' : Set (Fin n → ℝ)) = (eL.toLinearMap : V n →ₗ[ℝ] (Fin n → ℝ)) '' (Λ : Set (V n)) := rfl
    rw [hset, ← LinearMap.map_span, IsZLattice.span_top]
    ext y
    exact ⟨fun _ => trivial, fun _ => ⟨eL.symm y, trivial, eL.apply_symm_apply y⟩⟩
  have : IsZLattice ℝ L' := hL'_lat
  let b₀ := Module.Free.chooseBasis ℤ Λ
  let B₀ := b₀.ofZLatticeBasis ℝ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = n := by
    rw [← Module.finrank_eq_card_basis B₀, finrank_euclideanSpace_fin]
  let idx : Fin n ≃ Module.Free.ChooseBasisIndex ℤ Λ :=
    (Fintype.equivFinOfCardEq hcard).symm
  let bZ : Module.Basis (Fin n) ℤ Λ := b₀.reindex idx.symm
  let b : Fin n → V n := fun i => (bZ i : V n)
  have hb : IsLatticeBasis Λ b := by
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      have hgB : ∑ i : Fin n, g i • B₀ (idx i) = 0 := by
        convert hg using 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [b, bZ, B₀]
      exact Fintype.linearIndependent_iff.mp (B₀.linearIndependent.comp idx idx.injective) g hgB
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (bZ i).2
      · intro x hx
        let x₀ : Λ := ⟨x, hx⟩
        have hx₀ := (bZ.sum_repr x₀).symm
        have hval : x = ∑ i : Fin n, bZ.repr x₀ i • b i := by
          calc
            x = (x₀ : V n) := rfl
            _ = ((∑ i : Fin n, bZ.repr x₀ i • bZ i : Λ) : V n) := by rw [← hx₀]
            _ = ∑ i : Fin n, bZ.repr x₀ i • b i := by
              rw [AddSubmonoidClass.coe_finsetSum]
              rfl
        rw [hval]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let eZ : Λ ≃ₗ[ℤ] L' := LinearEquiv.ofBijective
    ((eL.toLinearMap.restrictScalars ℤ).restrict (p := Λ) (q := L') (fun x hx => ⟨x, hx, rfl⟩))
    ⟨fun a b hab => Subtype.ext (eL.injective (congrArg Subtype.val hab)),
     fun ⟨y, x, hx, hxy⟩ => ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  let bZ' : Module.Basis (Fin n) ℤ L' := bZ.map eZ
  have hcov_eq : ZLattice.covolume Λ = ZLattice.covolume L' := by
    let B₁ := bZ.ofZLatticeBasis ℝ Λ
    let B₂ := bZ'.ofZLatticeBasis ℝ L'
    let F := ZSpan.fundamentalDomain B₁
    let F' := ZSpan.fundamentalDomain B₂
    have hspan₁ : Submodule.span ℤ (Set.range B₁) = Λ := by
      have hr : Set.range B₁ = Set.range b := by
        ext x; simp [B₁, b]
      rw [hr, hb.2]
    have hspan₂ : Submodule.span ℤ (Set.range B₂) = L' := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp only [B₂, Module.Basis.ofZLatticeBasis_apply]
        exact (bZ' i).2
      · intro y hy
        let y₀ : L' := ⟨y, hy⟩
        have hy₀ := (bZ'.sum_repr y₀).symm
        have hval : y = ∑ i : Fin n, bZ'.repr y₀ i • B₂ i := by
          calc
            y = (y₀ : Fin n → ℝ) := rfl
            _ = ((∑ i : Fin n, bZ'.repr y₀ i • bZ' i : L') : Fin n → ℝ) := by rw [← hy₀]
            _ = ∑ i : Fin n, bZ'.repr y₀ i • (bZ' i : Fin n → ℝ) := by
              rw [AddSubmonoidClass.coe_finsetSum]
              rfl
            _ = ∑ i : Fin n, bZ'.repr y₀ i • B₂ i := by simp [B₂]
        rw [hval]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hfund : IsAddFundamentalDomain Λ.toAddSubgroup F volume := by
      have hf := ZSpan.isAddFundamentalDomain B₁ volume
      rwa [hspan₁] at hf
    have hfund' : IsAddFundamentalDomain L'.toAddSubgroup F' volume := by
      have hf := ZSpan.isAddFundamentalDomain B₂ volume
      rwa [hspan₂] at hf
    have hB_map : ∀ j : Fin n, eL (B₁ j) = B₂ j := by
      intro j
      simp only [B₁, B₂, Module.Basis.ofZLatticeBasis_apply, bZ', Module.Basis.map_apply]
      rfl
    have hF_img : eL ⁻¹' F' = F := by
      ext x
      simp only [F, F', ZSpan.mem_fundamentalDomain, Set.mem_preimage]
      have hrepr : ∀ i : Fin n, (B₂.repr (eL x)) i = (B₁.repr x) i := by
        intro i
        have hx := B₁.sum_repr x
        have heLx : eL x = ∑ j : Fin n, (B₁.repr x j) • B₂ j := by
          conv_lhs => rw [← hx]
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, hB_map j]
        conv_lhs => rw [heLx]
        simp [map_sum, map_smul, Module.Basis.repr_self]
      simp_rw [hrepr]
    rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hfund,
        ZLattice.covolume_eq_measure_fundamentalDomain L' volume hfund']
    have hm : MeasurableSet F' := ZSpan.fundamentalDomain_measurableSet B₂
    simp only [Measure.real, ← hF_img, hmp.measure_preimage hm.nullMeasurableSet]
  rw [hcov_eq, ZLattice.covolume_eq_det L' bZ', latticeDet_eq_of_isLatticeBasis hb]
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of (Subtype.val ∘ ⇑bZ')
  have hgram_M : Matrix.gram ℝ b = M * Mᵀ := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.of_apply,
      Function.comp_apply]
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    change (b j) l * (b i) l = ((bZ' i : Fin n → ℝ) l) * ((bZ' j : Fin n → ℝ) l)
    have hi : ((bZ' i : Fin n → ℝ) l) = (b i) l := rfl
    have hj : ((bZ' j : Fin n → ℝ) l) = (b j) l := rfl
    rw [hi, hj, mul_comm]
  rw [hgram_M, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]

lemma covolume_split {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (E : Submodule ℝ (V n)) (hE : IsLatticeSubspace Λ E) :
    ZLattice.covolume Λ = latticeDet (interSubspace Λ E) * latticeDet (projLattice Eᗮ Λ) := by
  have hdisc1 : DiscreteTopology (interSubspace Λ E) :=
    discrete_sublattice (interSubspace Λ E) inf_le_left
  have hE_orth : IsLatticeSubspace Λ Eᗮᗮ := by rwa [Submodule.orthogonal_orthogonal]
  have hdisc2 : DiscreteTopology (projLattice Eᗮ Λ) :=
    (LogConcaveLattice.Lift.lemma_2_2 n Λ Eᗮ).mpr hE_orth
  have : DiscreteTopology (interSubspace Λ E) := hdisc1
  have : DiscreteTopology (projLattice Eᗮ Λ) := hdisc2
  obtain ⟨k, b₁, hb₁⟩ := exists_isLatticeBasis (interSubspace Λ E)
  obtain ⟨m, b₂, hb₂⟩ := exists_isLatticeBasis (projLattice Eᗮ Λ)
  have hb₂_mem : ∀ j : Fin m, b₂ j ∈ projLattice Eᗮ Λ := by
    intro j
    rw [← hb₂.2]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose c hcΛ hcb₂ using fun j : Fin m => hb₂_mem j
  have hcb₂' : ∀ j : Fin m, Eᗮ.starProjection (c j) = b₂ j := hcb₂
  have hb₁_memE : ∀ i : Fin k, b₁ i ∈ E := by
    intro i
    have : b₁ i ∈ interSubspace Λ E := by
      rw [← hb₁.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact this.2
  have hb₁_memΛ : ∀ i : Fin k, b₁ i ∈ Λ := by
    intro i
    have : b₁ i ∈ interSubspace Λ E := by
      rw [← hb₁.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact this.1
  let Bsum : Sum (Fin k) (Fin m) → V n := Sum.elim b₁ c
  have hBsum_li : LinearIndependent ℝ Bsum := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Bsum, Sum.elim_inl, Sum.elim_inr] at hg
    have hg_proj : Eᗮ.starProjection (∑ i : Fin k, g (Sum.inl i) • b₁ i +
        ∑ j : Fin m, g (Sum.inr j) • c j) = 0 := by rw [hg, map_zero]
    rw [map_add, map_sum, map_sum] at hg_proj
    have hzero1 : ∑ i : Fin k, Eᗮ.starProjection (g (Sum.inl i) • b₁ i) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, (starProj_eq_zero_iff Eᗮ (b₁ i)).mpr
        (by rw [Submodule.orthogonal_orthogonal]; exact hb₁_memE i), smul_zero]
    rw [hzero1, zero_add] at hg_proj
    have hc_proj : ∑ j : Fin m, g (Sum.inr j) • b₂ j = 0 := by
      convert hg_proj using 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hcb₂' j]
    have hg2 : ∀ j : Fin m, g (Sum.inr j) = 0 :=
      Fintype.linearIndependent_iff.mp hb₂.1 (fun j => g (Sum.inr j)) hc_proj
    have hzero2 : ∑ j : Fin m, g (Sum.inr j) • c j = 0 := by
      refine Finset.sum_eq_zero fun j _ => by rw [hg2 j, zero_smul]
    rw [hzero2, add_zero] at hg
    have hg1 : ∀ i : Fin k, g (Sum.inl i) = 0 :=
      Fintype.linearIndependent_iff.mp hb₁.1 (fun i => g (Sum.inl i)) hg
    rintro (i | j)
    · exact hg1 i
    · exact hg2 j
  have hBsum_span : Submodule.span ℤ (Set.range Bsum) = Λ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i | j, rfl⟩
      · exact hb₁_memΛ i
      · exact hcΛ j
    · intro l hl
      have hl_proj : Eᗮ.starProjection l ∈ Submodule.span ℤ (Set.range b₂) := by
        rw [hb₂.2]
        exact ⟨l, hl, rfl⟩
      obtain ⟨z₂, hz₂⟩ := mem_span_range_exists_fun hl_proj
      let l' : V n := l - ∑ j : Fin m, z₂ j • c j
      have hl'Λ : l' ∈ Λ :=
        Submodule.sub_mem Λ hl (Submodule.sum_mem Λ fun j _ => Submodule.smul_mem Λ _ (hcΛ j))
      have hl'E : l' ∈ E := by
        rw [← Submodule.orthogonal_orthogonal E, ← starProj_eq_zero_iff Eᗮ]
        have hproj_sum : Eᗮ.starProjection (∑ j : Fin m, z₂ j • c j) =
            ∑ j : Fin m, z₂ j • b₂ j := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Int.cast_smul_eq_zsmul ℝ, map_smul, hcb₂' j, Int.cast_smul_eq_zsmul ℝ]
        simp [l', map_sub, hproj_sum, hz₂]
      have hl'_inter : l' ∈ Submodule.span ℤ (Set.range b₁) := by
        rw [hb₁.2]
        exact ⟨hl'Λ, hl'E⟩
      obtain ⟨z₁, hz₁⟩ := mem_span_range_exists_fun hl'_inter
      have hl_eq : l = ∑ i : Fin k, z₁ i • Bsum (Sum.inl i) +
          ∑ j : Fin m, z₂ j • Bsum (Sum.inr j) := by
        simp only [Bsum, Sum.elim_inl, Sum.elim_inr]
        rw [hz₁]
        simp [l']
      rw [hl_eq]
      exact Submodule.add_mem _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩))
  have hspan_Bsum_top : Submodule.span ℝ (Set.range Bsum) = ⊤ := by
    rw [← IsZLattice.span_top (K := ℝ) (L := Λ)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      apply Submodule.subset_span
      rw [← hBsum_span]
      exact Submodule.subset_span ⟨s, rfl⟩
    · rw [Submodule.span_le]
      intro x hx
      rw [← hBsum_span] at hx
      exact span_int_subset_span_real (Set.range Bsum) hx
  have hcard_sum : Fintype.card (Sum (Fin k) (Fin m)) = n := by
    have hfr := finrank_span_eq_card hBsum_li
    rw [hspan_Bsum_top, finrank_top, finrank_euclideanSpace_fin] at hfr
    exact hfr.symm
  let es : Fin n ≃ Sum (Fin k) (Fin m) := (Fintype.equivFinOfCardEq hcard_sum).symm
  let B : Fin n → V n := Bsum ∘ es
  have hB : IsLatticeBasis Λ B := by
    refine ⟨hBsum_li.comp es es.injective, ?_⟩
    have hrange : Set.range B = Set.range Bsum := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨es i, rfl⟩
      · rintro ⟨s, rfl⟩; exact ⟨es.symm s, by simp [B]⟩
    rw [hrange, hBsum_span]
  rw [covolume_eq_latticeDet Λ, latticeDet_eq_of_isLatticeBasis hB,
      latticeDet_eq_of_isLatticeBasis hb₁, latticeDet_eq_of_isLatticeBasis hb₂]
  have hgram_reindex : (Matrix.gram ℝ B).det = (Matrix.gram ℝ Bsum).det := by
    have hsub : Matrix.gram ℝ B = Matrix.submatrix (Matrix.gram ℝ Bsum) es es := rfl
    rw [hsub, Matrix.det_submatrix_equiv_self es]
  let G₁ := Matrix.gram ℝ b₁
  let G₂ := Matrix.gram ℝ b₂
  have hG₁pos : 0 < G₁.det := gram_det_pos hb₁.1
  have hspan_b₁ : Submodule.span ℝ (Set.range b₁) = E := by
    rw [span_real_of_isLatticeBasis hb₁, hE]
  have hcE_mem : ∀ j : Fin m, ∃ mcoef : Fin k → ℝ, ∑ i, mcoef i • b₁ i = E.starProjection (c j) := by
    intro j
    apply mem_span_range_exists_fun
    rw [hspan_b₁]
    exact starProj_mem E (c j)
  choose mcoef hmcoef using hcE_mem
  let M : Matrix (Fin k) (Fin m) ℝ := Matrix.of fun i j => mcoef j i
  have hc_decomp : ∀ j : Fin m, c j = (∑ i : Fin k, M i j • b₁ i) + b₂ j := by
    intro j
    have hd := (E.starProjection_add_starProjection_orthogonal (c j)).symm
    rw [← hmcoef j, hcb₂' j] at hd
    exact hd
  have hhorth_b₁_b₂ : ∀ (i : Fin k) (j : Fin m), ⟪b₁ i, b₂ j⟫ = 0 := by
    intro i j
    have hb₂E : b₂ j ∈ Eᗮ := by rw [← hcb₂' j]; exact starProj_mem Eᗮ (c j)
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' E (b₂ j)).mp hb₂E (b₁ i) (hb₁_memE i)
  let G₁₂ : Matrix (Fin k) (Fin m) ℝ := Matrix.of fun i j => ⟪b₁ i, c j⟫
  let G₂₁ : Matrix (Fin m) (Fin k) ℝ := Matrix.of fun j i => ⟪c j, b₁ i⟫
  let G₂₂ : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun j₁ j₂ => ⟪c j₁, c j₂⟫
  have hG₁₂ : G₁₂ = G₁ * M := by
    ext i j
    simp only [G₁₂, Matrix.of_apply, hc_decomp j, inner_add_right, hhorth_b₁_b₂ i j, add_zero,
      inner_sum, real_inner_smul_right, Matrix.mul_apply, G₁, Matrix.gram_apply]
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hG₂₁ : G₂₁ = Mᵀ * G₁ := by
    ext j i
    simp only [G₂₁, Matrix.of_apply, hc_decomp j, inner_add_left]
    have h0 : ⟪b₂ j, b₁ i⟫ = 0 := by rw [real_inner_comm]; exact hhorth_b₁_b₂ i j
    rw [h0, add_zero, sum_inner]
    simp [real_inner_smul_left, Matrix.mul_apply, Matrix.transpose_apply, G₁, Matrix.gram_apply]
  have hG₂₂ : G₂₂ = Mᵀ * G₁ * M + G₂ := by
    ext j₁ j₂
    simp only [G₂₂, Matrix.of_apply, hc_decomp j₁, hc_decomp j₂, inner_add_left, inner_add_right]
    have h01 : ⟪∑ i : Fin k, M i j₁ • b₁ i, b₂ j₂⟫ = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [real_inner_smul_left, hhorth_b₁_b₂ i j₂, mul_zero]
    have h02 : ⟪b₂ j₁, ∑ i : Fin k, M i j₂ • b₁ i⟫ = 0 := by
      rw [real_inner_comm, sum_inner]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [real_inner_smul_left, hhorth_b₁_b₂ i j₁, mul_zero]
    rw [h01, h02, add_zero, zero_add]
    congr 1
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      Matrix.mul_apply, Matrix.transpose_apply, G₁, Matrix.gram_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hblocks : Matrix.gram ℝ Bsum =
      Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 Mᵀ (1 : Matrix (Fin m) (Fin m) ℝ) *
      Matrix.fromBlocks G₁ 0 0 G₂ *
      Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) M 0 (1 : Matrix (Fin m) (Fin m) ℝ) := by
    have hb₀ : Matrix.gram ℝ Bsum = Matrix.fromBlocks G₁ G₁₂ G₂₁ G₂₂ := by
      ext (i₁ | j₁) (i₂ | j₂) <;> rfl
    rw [hb₀, hG₁₂, hG₂₁, hG₂₂, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hdet_sum : (Matrix.gram ℝ Bsum).det = G₁.det * G₂.det := by
    rw [hblocks, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂,
        Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [hgram_reindex, hdet_sum, Real.sqrt_mul (le_of_lt hG₁pos)]

end AuxLemma23

theorem solution (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (E : Submodule ℝ (V n)) (hE : IsLatticeSubspace Λ E) :
    ZLattice.covolume Λ = latticeDet (interSubspace Λ E) * latticeDet (projLattice Eᗮ Λ) ∧
      dual (projLattice Eᗮ Λ) = interSubspace (dual Λ) Eᗮ ∧
      IsLatticeSubspace (dual Λ) Eᗮ :=
  ⟨AuxLemma23.covolume_split Λ E hE,
   AuxLemma23.dual_projLattice Λ E,
   AuxLemma23.dual_latticeSubspace_of_proj Λ E hE⟩
