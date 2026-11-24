-- Prove2me | solution 1 for Leopoldt.exists_finiteIndex_units_ball
-- status  : ACCEPTED   (prove)
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T11:05:21.281353+00:00
-- url     : https://prove2.me/submissions/f131de6b-5a7d-4e55-a477-d8d1349c3ebc

import Definitions.Def_LeopoldtDefect

open NumberField IsDedekindDomain Leopoldt

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    ∃ u : Fin (Units.rank K) → (𝓞 K)ˣ,
      (Subgroup.closure (Set.range u)).FiniteIndex ∧
      ∀ (i : Fin (Units.rank K)) (v : PrimesOver p K),
        ‖((diagonalUnits p K (u i) v : v.1.adicCompletionIntegers K) :
          v.1.adicCompletion K) - 1‖ ≤ ‖((p : ℕ) : v.1.adicCompletion K)‖ ^ 2 := by
  let b := Units.basisModTorsion K
  have hsurj : Function.Surjective (QuotientGroup.mk' (Units.torsion K)) :=
    QuotientGroup.mk'_surjective _
  choose u₀ hu₀ using fun i => hsurj (Additive.toMul (b i))
  have hI : Ideal.span {(p : 𝓞 K) ^ 2} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero 2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hfin_quot : Finite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K) ^ 2}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have hfin_units : Finite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K) ^ 2})ˣ := inferInstance
  let N := Nat.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K) ^ 2})ˣ
  have hN_pos : 0 < N := Nat.card_pos
  refine ⟨fun i => u₀ i ^ N, ?_, ?_⟩
  · let H := Subgroup.closure (Set.range fun i => u₀ i ^ N)
    let f : Units.torsion K × (Fin (Units.rank K) → Fin N) → (𝓞 K)ˣ ⧸ H :=
      fun ⟨t, r⟩ => QuotientGroup.mk (t.1 * ∏ i, u₀ i ^ (r i : ℕ))
    have hf : Function.Surjective f := by
      rintro ⟨x⟩
      let _ := AddCommGroup.toIntModule (Additive ((𝓞 K)ˣ ⧸ Units.torsion K))
      let qx : Additive ((𝓞 K)ˣ ⧸ Units.torsion K) :=
        Additive.ofMul (QuotientGroup.mk' (Units.torsion K) x)
      let c := b.repr qx
      have hsum : ∑ i, c i • b i = qx := b.sum_repr qx
      let y₀ : (𝓞 K)ˣ := ∏ i, u₀ i ^ c i
      have hy₀ : QuotientGroup.mk' (Units.torsion K) y₀ = QuotientGroup.mk' (Units.torsion K) x := by
        have h1 : QuotientGroup.mk' (Units.torsion K) y₀ = Additive.toMul (∑ i, c i • b i) := by
          change (QuotientGroup.mk' (Units.torsion K)) (∏ i, u₀ i ^ c i) = Additive.toMul (∑ i, c i • b i)
          rw [map_prod, toMul_sum]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [map_zpow, hu₀ i, toMul_zsmul]
        rw [h1, hsum]
        rfl
      have hxy : x * y₀⁻¹ ∈ Units.torsion K := by
        rw [← QuotientGroup.eq_one_iff]
        change QuotientGroup.mk' (Units.torsion K) (x * y₀⁻¹) = 1
        rw [map_mul, map_inv, hy₀, mul_inv_cancel]
      let t : Units.torsion K := ⟨x * y₀⁻¹, hxy⟩
      let r : Fin (Units.rank K) → Fin N := fun i =>
        ⟨(c i % (N : ℤ)).toNat, by
          have h1 : 0 ≤ c i % (N : ℤ) := Int.emod_nonneg _ (Int.natCast_ne_zero.2 hN_pos.ne')
          have h2 : c i % (N : ℤ) < N := Int.emod_lt_of_pos _ (Int.natCast_pos.2 hN_pos)
          omega⟩
      refine ⟨⟨t, r⟩, ?_⟩
      change QuotientGroup.mk (t.1 * ∏ i, u₀ i ^ (r i : ℕ)) = QuotientGroup.mk x
      rw [QuotientGroup.eq]
      have hprod : y₀ = (∏ i, (u₀ i ^ N) ^ (c i / (N : ℤ))) * (∏ i, u₀ i ^ (r i : ℕ)) := by
        dsimp [y₀]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← zpow_natCast (u₀ i) N, ← zpow_mul, ← zpow_natCast (u₀ i) (r i : ℕ), ← zpow_add]
        congr 1
        have hr_eq : ((r i : ℕ) : ℤ) = c i % (N : ℤ) :=
          Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.2 hN_pos.ne'))
        rw [hr_eq, Int.mul_ediv_add_emod]
      have hH_mem : (∏ i, (u₀ i ^ N) ^ (c i / (N : ℤ))) ∈ H :=
        Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
      have heq_inv : (t.1 * ∏ i, u₀ i ^ (r i : ℕ))⁻¹ * x = ∏ i, (u₀ i ^ N) ^ (c i / (N : ℤ)) := by
        have hx_eq : x = t.1 * y₀ := by simp [t]
        rw [hx_eq, hprod, mul_inv_rev, mul_assoc]
        nth_rw 2 [← mul_assoc]
        rw [inv_mul_cancel, one_mul, mul_comm (∏ i, (u₀ i ^ N) ^ (c i / ↑N)), inv_mul_cancel_left]
      rw [heq_inv]
      exact hH_mem
    have : Finite (Units.torsion K × (Fin (Units.rank K) → Fin N)) := inferInstance
    have : Finite ((𝓞 K)ˣ ⧸ H) := Finite.of_surjective f hf
    exact Subgroup.finiteIndex_of_finite_quotient
  · intro i v
    have : Fintype (𝓞 K ⧸ Ideal.span {(p : 𝓞 K) ^ 2})ˣ := Fintype.ofFinite _
    have hq : Units.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K) ^ 2})).toMonoidHom (u₀ i ^ N) = 1 := by
      rw [map_pow]
      change (Units.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K) ^ 2})).toMonoidHom (u₀ i)) ^
        Nat.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K) ^ 2})ˣ = 1
      rw [Nat.card_eq_fintype_card]
      exact pow_card_eq_one
    have hmem : ((u₀ i ^ N : (𝓞 K)ˣ) : 𝓞 K) - 1 ∈ Ideal.span {(p : 𝓞 K) ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
      exact congrArg Units.val hq
    rcases Ideal.mem_span_singleton.1 hmem with ⟨y, hy⟩
    have hnorm_y : ‖algebraMap (𝓞 K) (v.1.adicCompletion K) y‖ ≤ 1 := by
      have hy_int : algebraMap (𝓞 K) (v.1.adicCompletion K) y ∈ v.1.adicCompletionIntegers K :=
        (algebraMap (𝓞 K) (v.1.adicCompletionIntegers K) y).2
      have hv : Valued.v (algebraMap (𝓞 K) (v.1.adicCompletion K) y) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v.1).1 hy_int
      exact Valued.toNormedField.norm_le_one_iff.2 hv
    have heq : ((diagonalUnits p K (u₀ i ^ N) v : v.1.adicCompletionIntegers K) :
        v.1.adicCompletion K) - 1 =
        ((p : ℕ) : v.1.adicCompletion K) ^ 2 * algebraMap (𝓞 K) (v.1.adicCompletion K) y := by
      have h1 : ((diagonalUnits p K (u₀ i ^ N) v : v.1.adicCompletionIntegers K) :
          v.1.adicCompletion K) = algebraMap (𝓞 K) (v.1.adicCompletion K) ((u₀ i ^ N : (𝓞 K)ˣ) : 𝓞 K) := by
        rfl
      rw [h1, ← map_one (algebraMap (𝓞 K) (v.1.adicCompletion K)), ← map_sub, hy, map_mul, map_pow, map_natCast]
    rw [heq, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hnorm_y
