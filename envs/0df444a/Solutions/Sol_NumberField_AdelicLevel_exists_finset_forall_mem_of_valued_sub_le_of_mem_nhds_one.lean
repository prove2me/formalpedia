-- Prove2me | solution 1 for NumberField.AdelicLevel.exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e22e522a-25c2-54bd-8a22-d4f344d6331c

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped Topology

namespace R4FiLevel

variable {K : Type} [Field K] [NumberField K]

theorem exists_nat_setOf_valued_le_subset (v : HeightOneSpectrum (𝓞 K))
    (s : Set (v.adicCompletion K)) (hs : s ∈ 𝓝 (0 : v.adicCompletion K)) :
    ∃ e : ℕ, {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(e : ℤ))} ⊆ s := by
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hball⟩ := hs
  have hN : 1 < (Ideal.absNorm v.asIdeal : NNReal) := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hN0 : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 := ne_zero_of_lt hN
  have hq : ((Ideal.absNorm v.asIdeal : NNReal) : ℝ)⁻¹ < 1 := by
    have : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) := by exact_mod_cast hN
    exact inv_lt_one_of_one_lt₀ this
  have hq0 : 0 ≤ ((Ideal.absNorm v.asIdeal : NNReal) : ℝ)⁻¹ := by positivity
  obtain ⟨e, he⟩ := exists_pow_lt_of_lt_one hε hq
  refine ⟨e, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hnorm : ‖y‖ = (WithZeroMulInt.toNNReal hN0 (Valued.v y) : ℝ) :=
    NumberField.FinitePlace.norm_def v y
  have hmono := (WithZeroMulInt.toNNReal_strictMono hN).monotone hy
  have hval : (WithZeroMulInt.toNNReal hN0 (WithZero.exp (-(e : ℤ))) : ℝ)
      = ((Ideal.absNorm v.asIdeal : NNReal) : ℝ)⁻¹ ^ e := by
    rw [WithZeroMulInt.toNNReal_neg_apply hN0 (WithZero.exp_ne_zero)]
    simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_natCast, NNReal.coe_inv,
      NNReal.coe_pow, inv_pow]
  calc ‖y‖ = (WithZeroMulInt.toNNReal hN0 (Valued.v y) : ℝ) := hnorm
    _ ≤ (WithZeroMulInt.toNNReal hN0 (WithZero.exp (-(e : ℤ))) : ℝ) := by exact_mod_cast hmono
    _ = ((Ideal.absNorm v.asIdeal : NNReal) : ℝ)⁻¹ ^ e := hval
    _ < ε := he

end R4FiLevel

namespace R4FiLevel

variable {K : Type} [Field K] [NumberField K]

theorem exists_finset_nat_subset_of_mem_nhds_zero
    (s : Set (FiniteAdeleRing (𝓞 K) K)) (hs : s ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (e : ℕ),
      ∀ y : FiniteAdeleRing (𝓞 K) K,
        (∀ v, y v ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ T, Valued.v (y v) ≤ WithZero.exp (-(e : ℤ))) → y ∈ s := by
  classical
  let Rv : HeightOneSpectrum (𝓞 K) → Type := fun v => v.adicCompletion K
  let A : (v : HeightOneSpectrum (𝓞 K)) → Set (Rv v) := fun v =>
    (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hAopen : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  let x₀ : (v : HeightOneSpectrum (𝓞 K)) → A v := fun v => ⟨0, (v.adicCompletionIntegers K).zero_mem⟩
  have hx₀ : RestrictedProduct.structureMap Rv A Filter.cofinite x₀ = (0 : FiniteAdeleRing (𝓞 K) K) :=
    RestrictedProduct.ext _ _ fun _ => rfl
  have hnhds := RestrictedProduct.nhds_eq_map_structureMap (R := Rv) (A := A) hAopen x₀
  rw [hx₀] at hnhds
  have hs' : (RestrictedProduct.structureMap Rv A Filter.cofinite) ⁻¹' s ∈ 𝓝 x₀ := by
    have : s ∈ Filter.map (RestrictedProduct.structureMap Rv A Filter.cofinite) (𝓝 x₀) := hnhds ▸ hs
    exact this
  rw [nhds_pi, Filter.mem_pi'] at hs'
  obtain ⟨I, t, ht, hIt⟩ := hs'
  have hloc : ∀ v, ∃ e : ℕ, ∀ z : A v,
      Valued.v (z : v.adicCompletion K) ≤ WithZero.exp (-(e : ℤ)) → z ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨e, he⟩ := exists_nat_setOf_valued_le_subset v u hu
    exact ⟨e, fun z hz => hut (he hz)⟩
  choose e he using hloc
  refine ⟨I, I.sup e, fun y hy hyT => ?_⟩
  let x : (v : HeightOneSpectrum (𝓞 K)) → A v := fun v => ⟨y v, hy v⟩
  have hxy : RestrictedProduct.structureMap Rv A Filter.cofinite x = y :=
    RestrictedProduct.ext _ _ fun _ => rfl
  have hx : x ∈ Set.pi (↑I) t := by
    intro v hv
    refine he v (x v) ((hyT v hv).trans ?_)
    rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
    exact Finset.le_sup (f := e) hv
  have := hIt hx
  rwa [Set.mem_preimage, hxy] at this

end R4FiLevel

namespace R4FiLevel

variable {K : Type} [Field K] [NumberField K]

theorem exists_entry_nhds_of_mem_nhds_matrix {A : Type*} [TopologicalSpace A]
    (M₀ : Matrix (Fin 2) (Fin 2) A) (O : Set (Matrix (Fin 2) (Fin 2) A)) (hO : O ∈ 𝓝 M₀) :
    ∃ E : Fin 2 → Fin 2 → Set A, (∀ i j, E i j ∈ 𝓝 (M₀ i j)) ∧
      ∀ M : Matrix (Fin 2) (Fin 2) A, (∀ i j, M i j ∈ E i j) → M ∈ O := by
  have h : O ∈ Filter.pi fun i => 𝓝 (M₀ i) := by rw [← nhds_pi]; exact hO
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.1 h
  have hrow : ∀ i, ∃ r : Fin 2 → Set A, (∀ j, r j ∈ 𝓝 (M₀ i j)) ∧
      ∀ x : Fin 2 → A, (∀ j, x j ∈ r j) → x ∈ t i := by
    intro i
    have hi : t i ∈ Filter.pi fun j => 𝓝 (M₀ i j) := by rw [← nhds_pi]; exact ht i
    obtain ⟨J, r, hr, hJr⟩ := Filter.mem_pi'.1 hi
    exact ⟨r, hr, fun x hx => hJr fun j _ => hx j⟩
  choose r hr hrt using hrow
  refine ⟨r, hr, fun M hM => hIt fun i _ => hrt i (M i) fun j => hM i j⟩

theorem exists_finset_nat_forall_mem_of_mem_nhds_one
    (V : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hV : V ∈ 𝓝 (1 : GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (e : ℕ),
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), glArch (𝓞 K) K g = 1 →
        (∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2),
          ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K ∧
          (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
            ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ T, ∀ i j : Fin 2,
          Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
              - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(e : ℤ)) ∧
          Valued.v ((((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
              - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(e : ℤ))) →
        g ∈ V := by
  classical

  set M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) with hM
  rw [Units.isInducing_embedProduct.nhds_eq_comap] at hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.1 hV
  have h1 : Units.embedProduct M 1 = ((1 : M), MulOpposite.op (1 : M)) := by
    simp [Units.embedProduct]
  rw [h1, mem_nhds_prod_iff] at hW
  obtain ⟨u₁, hu₁, u₂, hu₂, huW⟩ := hW
  have hu₂' : MulOpposite.op ⁻¹' u₂ ∈ 𝓝 (1 : M) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hu₂
  set W₁ : Set M := u₁ ∩ MulOpposite.op ⁻¹' u₂ with hW₁
  have hW₁ : W₁ ∈ 𝓝 (1 : M) := Filter.inter_mem hu₁ hu₂'
  have hkey : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), (g : M) ∈ W₁ →
      ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : M) ∈ W₁ → g ∈ V := by
    intro g hg hgi
    apply hWV
    rw [Set.mem_preimage, Units.embedProduct_apply]
    exact huW (Set.mk_mem_prod hg.1 hgi.2)

  obtain ⟨E, hE, hEW⟩ := exists_entry_nhds_of_mem_nhds_matrix (1 : M) W₁ hW₁

  have hfin : ∀ i j : Fin 2, ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (e : ℕ),
      ∀ x : AdeleRing (𝓞 K) K, x.1 = ((1 : M) i j).1 →
        (∀ v, x.2 v - ((1 : M) i j).2 v ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ T, Valued.v (x.2 v - ((1 : M) i j).2 v) ≤ WithZero.exp (-(e : ℤ))) → x ∈ E i j := by
    intro i j
    set c : AdeleRing (𝓞 K) K := (1 : M) i j with hc
    obtain ⟨Ea, hEa, Ef, hEf, hEE⟩ := mem_nhds_prod_iff.1 (hE i j)
    have hEf0 : (fun y : FiniteAdeleRing (𝓞 K) K => y + c.2) ⁻¹' Ef ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := by
      refine (continuous_add_const c.2).continuousAt.preimage_mem_nhds ?_
      rwa [zero_add]
    obtain ⟨T, e, hTe⟩ := exists_finset_nat_subset_of_mem_nhds_zero _ hEf0
    refine ⟨T, e, fun x hx1 hxi hxT => ?_⟩
    have hx : x = (x.1, x.2) := rfl
    rw [hx]
    refine hEE (Set.mk_mem_prod ?_ ?_)
    · rw [hx1]; exact mem_of_mem_nhds hEa
    · have h := hTe (x.2 - c.2) (fun v => hxi v) (fun v hv => hxT v hv)
      simpa using h
  choose T e hTe using hfin
  refine ⟨Finset.univ.biUnion fun p : Fin 2 × Fin 2 => T p.1 p.2,
    Finset.univ.sup fun p : Fin 2 × Fin 2 => e p.1 p.2, fun g hg hint hlev => ?_⟩

  have hone : ∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2),
      ((1 : M) i j).2 v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro v i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]; rfl
  have hone1 : ∀ i j : Fin 2, ((1 : M) i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]; rfl
  have hmemT : ∀ (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)), v ∈ T i j →
      v ∈ Finset.univ.biUnion fun p : Fin 2 × Fin 2 => T p.1 p.2 := fun i j v hv =>
    Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, hv⟩
  have hle : ∀ i j : Fin 2, e i j ≤ Finset.univ.sup fun p : Fin 2 × Fin 2 => e p.1 p.2 := fun i j =>
    Finset.le_sup (f := fun p : Fin 2 × Fin 2 => e p.1 p.2) (Finset.mem_univ (i, j))
  have hexp : ∀ i j : Fin 2, WithZero.exp (-((Finset.univ.sup fun p : Fin 2 × Fin 2 => e p.1 p.2 : ℕ) : ℤ))
      ≤ WithZero.exp (-(e i j : ℤ)) := by
    intro i j
    rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
    exact hle i j
  have hsub1 : ∀ (v : HeightOneSpectrum (𝓞 K)) (a : v.adicCompletion K) (b : v.adicCompletion K),
      a ∈ v.adicCompletionIntegers K → Valued.v b ≤ 1 → a - b ∈ v.adicCompletionIntegers K := by
    intro v a b ha hb
    exact (v.adicCompletionIntegers K).sub_mem ha ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hb)
  have hone_le : ∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2),
      Valued.v ((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 := by
    intro v i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  refine hkey g (hEW _ fun i j => ?_) (hEW _ fun i j => ?_)
  · refine hTe i j _ ?_ (fun v => ?_) (fun v hv => ?_)
    · rw [hone1, ← glArch_apply, hg]; rfl
    · rw [hone]; exact hsub1 v _ _ (hint v i j).1 (hone_le v i j)
    · rw [hone]; exact ((hlev v (hmemT i j v hv) i j).1).trans (hexp i j)
  · refine hTe i j _ ?_ (fun v => ?_) (fun v hv => ?_)
    · have hg' : glArch (𝓞 K) K g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
      rw [hone1, ← glArch_apply, hg']; rfl
    · rw [hone]; exact hsub1 v _ _ (hint v i j).2 (hone_le v i j)
    · rw [hone]; exact ((hlev v (hmemT i j v hv) i j).2).trans (hexp i j)

end R4FiLevel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (V : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (_hV : V ∈ 𝓝 (1 : GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (e : ℕ),
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), glArch (𝓞 K) K g = 1 →
        (∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2),
          ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K ∧
          (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
            ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ T, ∀ i j : Fin 2,
          Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
              - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(e : ℤ)) ∧
          Valued.v ((((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
              - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(e : ℤ))) →
        g ∈ V :=
  R4FiLevel.exists_finset_nat_forall_mem_of_mem_nhds_one V _hV

end S_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
end P2MW
export P2MW.S_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one (solution)
