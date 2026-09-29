-- Prove2me | solution 1 for LaurentSeries.exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ee7ffee1-7b2f-57b9-b274-634fdd46611b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite

set_option autoImplicit false

open Module

namespace LaurentSeries
namespace Cart
p2m_open "LaurentSeries"

variable {F : Type*} [Field F] (O : ValuationSubring F) [IsDiscreteValuationRing O]

theorem exists_coeff_dvd (g : LaurentSeries F) (hg : g ≠ 0) (hint : ∀ n : ℤ, g.coeff n ∈ O) :
    ∃ n₀ : ℤ, g.coeff n₀ ≠ 0 ∧ ∀ n : ℤ, ∃ t : F, t ∈ O ∧ g.coeff n = g.coeff n₀ * t := by
  classical
  let S : Set ℕ∞ := {v | ∃ n, g.coeff n ≠ 0 ∧ IsDiscreteValuationRing.addVal O ⟨g.coeff n, hint n⟩ = v}
  have hne : S.Nonempty := by
    obtain ⟨n, hn⟩ : ∃ n, g.coeff n ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (HahnSeries.ext (funext h))
    exact ⟨_, n, hn, rfl⟩
  obtain ⟨v₀, ⟨n₀, hn₀, hv₀⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hne
  refine ⟨n₀, hn₀, fun n => ?_⟩
  by_cases hn : g.coeff n = 0
  · exact ⟨0, O.zero_mem, by rw [hn, mul_zero]⟩
  have hle : IsDiscreteValuationRing.addVal O ⟨g.coeff n₀, hint n₀⟩
      ≤ IsDiscreteValuationRing.addVal O ⟨g.coeff n, hint n⟩ := by
    rw [hv₀]
    exact not_lt.mp (hmin _ ⟨n, hn, rfl⟩)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp hle
  refine ⟨t, t.2, ?_⟩
  have := congrArg Subtype.val ht
  simpa using this

theorem coeff_linearMap_apply (n : ℤ) (x : LaurentSeries F) :
    (HahnSeries.coeff.linearMap (R := F) n) x = x.coeff n := rfl

theorem coeff_sum_smul {ι : Type*} (s : Finset ι) (c : ι → F) (x : ι → LaurentSeries F) (n : ℤ) :
    (∑ i ∈ s, c i • x i).coeff n = ∑ i ∈ s, c i * (x i).coeff n := by
  rw [← coeff_linearMap_apply (F := F) n, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, coeff_linearMap_apply]

theorem exists_family (d : ℕ) : ∀ (V : Submodule F (LaurentSeries F)), FiniteDimensional F V →
    finrank F V = d →
    (∀ f ∈ V, ∃ c : F, c ≠ 0 ∧ ∀ n : ℤ, c * (f : LaurentSeries F).coeff n ∈ O) →
    ∃ (b : Fin d → LaurentSeries F) (p : Fin d → ℤ), (∀ i, b i ∈ V) ∧ (∀ i n, (b i).coeff n ∈ O) ∧
      ∀ i j, (b j).coeff (p i) = if i = j then 1 else 0 := by
  classical
  induction d with
  | zero =>
    intro V _ _ _
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ d ih =>
    intro V hfd hdim hbdd
    haveI := hfd

    obtain ⟨f, hfV, hf0⟩ : ∃ f ∈ V, f ≠ 0 := by
      have hpos : 0 < finrank F V := by omega
      obtain ⟨⟨f, hfV⟩, hf⟩ := finrank_pos_iff_exists_ne_zero.mp hpos
      exact ⟨f, hfV, fun h => hf (Subtype.ext h)⟩
    obtain ⟨c, hc0, hc⟩ := hbdd f hfV
    set g : LaurentSeries F := c • f with hgdef
    have hgV : g ∈ V := V.smul_mem c hfV
    have hg0 : g ≠ 0 := smul_ne_zero hc0 hf0
    have hgint : ∀ n, g.coeff n ∈ O := fun n => by
      rw [hgdef, HahnSeries.coeff_smul, smul_eq_mul]; exact hc n
    obtain ⟨n₀, hn₀, hdiv⟩ := exists_coeff_dvd O g hg0 hgint
    choose t htO ht using hdiv

    set b₀ : LaurentSeries F := (g.coeff n₀)⁻¹ • g with hb₀def
    have hb₀V : b₀ ∈ V := V.smul_mem _ hgV
    have hb₀coeff : ∀ n, b₀.coeff n = t n := fun n => by
      rw [hb₀def, HahnSeries.coeff_smul, smul_eq_mul, ht n, ← mul_assoc, inv_mul_cancel₀ hn₀, one_mul]
    have hb₀int : ∀ n, b₀.coeff n ∈ O := fun n => (hb₀coeff n) ▸ htO n
    have hb₀n₀ : b₀.coeff n₀ = 1 := by
      rw [hb₀def, HahnSeries.coeff_smul, smul_eq_mul, inv_mul_cancel₀ hn₀]

    let φ : LaurentSeries F →ₗ[F] F := HahnSeries.coeff.linearMap (R := F) n₀
    have hφ : ∀ x : LaurentSeries F, φ x = x.coeff n₀ := fun x => rfl
    let ψ : V →ₗ[F] F := φ.comp V.subtype
    have hψ : ∀ x : V, ψ x = (x : LaurentSeries F).coeff n₀ := fun x => rfl
    let W : Submodule F (LaurentSeries F) := (LinearMap.ker ψ).map V.subtype
    have hWV : W ≤ V := Submodule.map_subtype_le V _
    have hmemW : ∀ x, x ∈ W ↔ x ∈ V ∧ x.coeff n₀ = 0 := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, hψ] at hy
        exact ⟨y.2, hy⟩
      · rintro ⟨hxV, hx0⟩
        refine ⟨⟨x, hxV⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, hψ]
        exact hx0
    haveI : FiniteDimensional F W := Submodule.finiteDimensional_of_le hWV
    have hdimW : finrank F W = d := by
      have h1 : finrank F W = finrank F (LinearMap.ker ψ) := Submodule.finrank_map_subtype_eq V _
      have h2 := LinearMap.finrank_range_add_finrank_ker ψ
      have h3 : finrank F (LinearMap.range ψ) = 1 := by
        have hsurj : LinearMap.range ψ = ⊤ := by
          rw [LinearMap.range_eq_top]
          intro r
          refine ⟨r • ⟨b₀, hb₀V⟩, ?_⟩
          rw [map_smul, hψ, smul_eq_mul]
          change r * b₀.coeff n₀ = r
          rw [hb₀n₀, mul_one]
        rw [hsurj, finrank_top, Module.finrank_self]
      omega

    obtain ⟨b', p', hb'W, hb'int, hb'δ⟩ := ih W inferInstance hdimW (fun f hf => hbdd f (hWV hf))
    have hb'n₀ : ∀ i, (b' i).coeff n₀ = 0 := fun i => ((hmemW _).mp (hb'W i)).2
    have hb'V : ∀ i, b' i ∈ V := fun i => ((hmemW _).mp (hb'W i)).1

    set b₀' : LaurentSeries F := b₀ - ∑ i, (b₀.coeff (p' i)) • b' i with hb₀'def
    have hcomb : ∀ n, b₀'.coeff n = b₀.coeff n - ∑ i, b₀.coeff (p' i) * (b' i).coeff n := by
      intro n
      rw [hb₀'def, HahnSeries.coeff_sub, coeff_sum_smul]
    refine ⟨Fin.cons b₀' b', Fin.cons n₀ p', ?_, ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_)
      · rw [Fin.cons_zero]
        exact V.sub_mem hb₀V (V.sum_mem fun i _ => V.smul_mem _ (hb'V i))
      · rw [Fin.cons_succ]; exact hb'V i
    · refine Fin.cases (fun n => ?_) (fun i n => ?_)
      · rw [Fin.cons_zero, hcomb]
        exact sub_mem (hb₀int n) (sum_mem fun i _ => mul_mem (hb₀int _) (hb'int i n))
      · rw [Fin.cons_succ]; exact hb'int i n
    · refine Fin.cases ?_ (fun i => ?_)
      ·
        refine Fin.cases ?_ (fun j => ?_)
        · rw [Fin.cons_zero, Fin.cons_zero, if_pos rfl, hcomb, hb₀n₀]
          simp only [hb'n₀, mul_zero, Finset.sum_const_zero, sub_zero]
        · rw [Fin.cons_zero, Fin.cons_succ, if_neg (Fin.succ_ne_zero j).symm]
          exact hb'n₀ j
      ·
        refine Fin.cases ?_ (fun j => ?_)
        · rw [Fin.cons_succ, Fin.cons_zero, if_neg (Fin.succ_ne_zero i), hcomb]
          have : ∑ k, b₀.coeff (p' k) * (b' k).coeff (p' i) = b₀.coeff (p' i) := by
            rw [Finset.sum_eq_single i]
            · rw [hb'δ i i, if_pos rfl, mul_one]
            · intro k _ hk
              rw [hb'δ i k, if_neg (Ne.symm hk), mul_zero]
            · intro h; exact absurd (Finset.mem_univ i) h
          rw [this, sub_self]
        · rw [Fin.cons_succ, Fin.cons_succ, hb'δ i j]
          by_cases hij : i = j
          · subst hij; simp
          · rw [if_neg hij, if_neg (fun h => hij (Fin.succ_inj.mp h))]

end LaurentSeries.Cart

open LaurentSeries.Cart in
theorem solution
    {F : Type*} [Field F] (O : ValuationSubring F) [IsDiscreteValuationRing O]
    (V : Submodule F (LaurentSeries F)) [FiniteDimensional F V]
    (hbdd : ∀ f ∈ V, ∃ c : F, c ≠ 0 ∧ ∀ n : ℤ, c * (f : LaurentSeries F).coeff n ∈ O) :
    ∃ (b : Module.Basis (Fin (Module.finrank F V)) F V) (p : Fin (Module.finrank F V) → ℤ),
      (∀ (i : Fin (Module.finrank F V)) (n : ℤ), ((b i : V) : LaurentSeries F).coeff n ∈ O) ∧
      ∀ i j : Fin (Module.finrank F V),
        ((b j : V) : LaurentSeries F).coeff (p i) = if i = j then 1 else 0 := by
  classical
  obtain ⟨b, p, hbV, hbint, hbδ⟩ := exists_family O (finrank F V) V inferInstance rfl hbdd
  let bV : Fin (finrank F V) → V := fun i => ⟨b i, hbV i⟩
  have hli : LinearIndependent F bV := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 := congrArg (fun x : V => (x : LaurentSeries F).coeff (p i)) hs
    simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h0
    rw [coeff_sum_smul] at h0
    rw [Finset.sum_eq_single i] at h0
    · change g i * (b i).coeff (p i) = 0 at h0
      rwa [hbδ i i, if_pos rfl, mul_one] at h0
    · intro k _ hk
      change g k * (b k).coeff (p i) = 0
      rw [hbδ i k, if_neg (Ne.symm hk), mul_zero]
    · intro h; exact absurd hi h
  have hsp : ⊤ ≤ Submodule.span F (Set.range bV) := by
    rw [top_le_iff]
    exact hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin])
  refine ⟨Module.Basis.mk hli hsp, p, fun i n => ?_, fun i j => ?_⟩
  · rw [Module.Basis.mk_apply]; exact hbint i n
  · rw [Module.Basis.mk_apply]; exact hbδ i j

end S_LaurentSeries_exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite
end P2MW
export P2MW.S_LaurentSeries_exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite (solution)
