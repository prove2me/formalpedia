-- Prove2me | solution 1 for MvFormalGroup.finrank_quotient_span_nthSeries_pow_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7cb12762-c06d-53ac-a0df-56049dcbc305

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open MvPowerSeries

universe u

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm End nthSeries mk End.toPowerSeries_one End.toPowerSeries_mul End.toPowerSeries_natCast constantCoeff_nthSeries"
namespace T1ab
p2m_open "MvFormalGroup"

open MvPowerSeries

variable {k : Type u} [Field k] {d : ℕ}

private theorem comp_basis {A : Type u} [CommRing A] (θ θ' : A →+* A) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (B : ι → A) (b : ι' → A)
    (hB : ∀ x, ∃! c : ι → A, x = ∑ J, θ (c J) * B J)
    (hb : ∀ x, ∃! c : ι' → A, x = ∑ j, θ' (c j) * b j) :
    ∀ x, ∃! c : ι × ι' → A, x = ∑ q, θ (θ' (c q)) * (θ (b q.2) * B q.1) := by
  intro x
  obtain ⟨c, hc, hcu⟩ := hB x
  choose e he heu using fun J => hb (c J)
  refine ⟨fun q => e q.1 q.2, ?_, ?_⟩
  · show x = ∑ q : ι × ι', θ (θ' (e q.1 q.2)) * (θ (b q.2) * B q.1)
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [hc]
    refine Finset.sum_congr rfl fun J _ => ?_
    conv_lhs => rw [he J, map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  · intro c' hc'

    have h1 : x = ∑ J, θ (∑ j, θ' (c' (J, j)) * b j) * B J := by
      rw [hc', Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      ring
    have h2 : (fun J => ∑ j, θ' (c' (J, j)) * b j) = c := hcu _ h1
    funext q
    have h3 : (fun j => c' (q.1, j)) = e q.1 := heu q.1 _ (by rw [← congrFun h2 q.1])
    exact congrFun h3 q.2

private theorem mem_span_X_pow {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ] (N : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ R) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries σ R) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

private theorem mem_span_range_X_of_constantCoeff {R : Type*} [CommRing R] {f : MvPowerSeries (Fin d) R}
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) := by
  classical
  have h := mem_span_X_pow 1 Finset.univ f fun e he => by
    have : e = 0 := by
      ext s
      have := he s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [this, coeff_zero_eq_constantCoeff_apply, hf]
  simpa only [pow_one, Finset.coe_univ, Set.image_univ] using h

private theorem constantCoeff_eq_zero_of_mem_span_range_X {R : Type*} [CommRing R] {f : MvPowerSeries (Fin d) R}
    (hf : f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R))) : constantCoeff f = 0 := by
  have hle : Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) ≤
      RingHom.ker (constantCoeff : MvPowerSeries (Fin d) R →+* R) := by
    rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    exact constantCoeff_X s
  exact hle hf

private theorem finrank_quotient_eq_card {g : Fin d → MvPowerSeries (Fin d) k} (hg : ∀ i, constantCoeff (g i) = 0)
    {ι : Type} [Fintype ι] (B : ι → MvPowerSeries (Fin d) k)
    (hB : ∀ x, ∃! c : ι → MvPowerSeries (Fin d) k, x = ∑ i, subst g (c i) * B i) :
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) = Fintype.card ι := by
  classical
  let θ : MvPowerSeries (Fin d) k →ₐ[k] MvPowerSeries (Fin d) k := substAlgHom (hasSubst_of_constantCoeff_zero hg)
  have hθ : ∀ x, θ x = subst g x := fun x => by show substAlgHom _ x = _; rw [coe_substAlgHom]
  have hθX : ∀ i, θ (X i) = g i := fun i => by rw [hθ, subst_X (hasSubst_of_constantCoeff_zero hg)]
  have hθC : ∀ c : k, θ (C c) = C c := fun c => by rw [c_eq_algebraMap, AlgHom.commutes]
  have hrg : (⇑θ) '' Set.range (X : Fin d → MvPowerSeries (Fin d) k) = Set.range g := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hθX)
  let πg := Ideal.Quotient.mk (Ideal.span (Set.range g))
  have hπC : ∀ c : k, πg (C c) = algebraMap k _ c := fun c => by
    rw [IsScalarTower.algebraMap_apply k (MvPowerSeries (Fin d) k) (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)),
      Ideal.Quotient.algebraMap_eq, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hθmod : ∀ r, πg (subst g r) = algebraMap k _ (constantCoeff r) := by
    intro r
    have hr : r - C (constantCoeff r) ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k)) :=
      mem_span_range_X_of_constantCoeff (by rw [map_sub, constantCoeff_C, sub_self])
    have h1 : θ r - C (constantCoeff r) ∈ Ideal.span (Set.range g) := by
      rw [← hθC, ← map_sub]
      have h2 := Ideal.mem_map_of_mem θ hr
      rwa [Ideal.map_span, hrg] at h2
    rw [← hθ, ← hπC, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.neg_mem_iff, neg_sub]
    exact h1
  let ev : ι → MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g) := fun i => πg (B i)
  have hspan : ⊤ ≤ Submodule.span k (Set.range ev) := by
    rintro y -
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc, -⟩ := hB x
    rw [hc, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_mul, hθmod, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent k ev := by
    rw [Fintype.linearIndependent_iff]
    intro l hl i₀

    have hz : ∑ i, C (l i) * B i ∈ Ideal.span (Set.range g) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hl]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hπC, ← Algebra.smul_def]

    obtain ⟨y, hy⟩ := Ideal.mem_span_range_iff_exists_fun.mp hz
    choose cy hcy _ using fun j => hB (y j)
    have hz2 : ∑ i, C (l i) * B i = ∑ i, subst g (∑ j, X j * cy j i) * B i := by
      rw [← hy]
      have hsub : ∀ i, subst g (∑ j, X j * cy j i) = ∑ j, g j * subst g (cy j i) := fun i => by
        rw [← hθ, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, hθX, hθ]
      simp_rw [hsub, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcy j, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hz3 : ∑ i, C (l i) * B i = ∑ i, subst g (C (l i)) * B i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hθ, hθC]
    obtain ⟨c0, -, hc0u⟩ := hB (∑ i, C (l i) * B i)
    have e1 := hc0u _ hz3
    have e2 := hc0u _ hz2
    have heq : C (l i₀) = ∑ j, X j * cy j i₀ := by
      have := congrFun (e1.trans e2.symm) i₀
      exact this
    have hmem : (C (l i₀) : MvPowerSeries (Fin d) k) ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k)) := by
      rw [heq]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have := constantCoeff_eq_zero_of_mem_span_range_X hmem
    rwa [constantCoeff_C] at this
  exact Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)

end MvFormalGroup.T1ab

theorem solution
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] {d : ℕ} (F : MvFormalGroup d k) [F.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (F.nthSeries p))) = p ^ h)
    (v : ℕ) :
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) =
      p ^ (v * h) := by
  classical

  have h0 : ∀ n i, MvPowerSeries.constantCoeff (F.nthSeries n i) = 0 := fun n => MvFormalGroup.constantCoeff_nthSeries F n

  have hcomp : ∀ (v : ℕ) (x : MvPowerSeries (Fin d) k),
      subst (F.nthSeries (p ^ v)) (subst (F.nthSeries p) x) = subst (F.nthSeries (p ^ (v + 1))) x := by
    intro v x
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (h0 p)) (hasSubst_of_constantCoeff_zero (h0 (p ^ v)))]
    congr 1
    have h := MvFormalGroup.End.toPowerSeries_mul F ((p : MvFormalGroup.End F)) (((p ^ v : ℕ) : MvFormalGroup.End F))
    rw [MvFormalGroup.End.toPowerSeries_natCast, ← Nat.cast_mul, MvFormalGroup.End.toPowerSeries_natCast,
      MvFormalGroup.End.toPowerSeries_natCast, ← pow_succ'] at h
    exact h.symm

  haveI hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (F.nthSeries p))) :=
    Module.finite_of_finrank_pos (by rw [hh]; exact pow_pos (Fact.out : p.Prime).pos h)
  obtain ⟨-, -, b, hb⟩ := MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient (F.nthSeries p) (h0 p) hfin

  have key : ∀ v : ℕ, ∃ (ι : Type) (_ : Fintype ι) (B : ι → MvPowerSeries (Fin d) k),
      Fintype.card ι = (p ^ h) ^ v ∧
      ∀ x, ∃! c : ι → MvPowerSeries (Fin d) k, x = ∑ i, subst (F.nthSeries (p ^ v)) (c i) * B i := by
    intro v
    induction v with
    | zero =>
      have h1 : F.nthSeries 1 = (X : Fin d → MvPowerSeries (Fin d) k) := by
        rw [← MvFormalGroup.End.toPowerSeries_natCast, Nat.cast_one, MvFormalGroup.End.toPowerSeries_one]
      have hid : ∀ x : MvPowerSeries (Fin d) k, subst (F.nthSeries 1) x = x := fun x => by
        rw [h1]; exact congrFun subst_self x
      refine ⟨Unit, inferInstance, fun _ => 1, by simp, fun x => ⟨fun _ => x, ?_, ?_⟩⟩
      · show x = ∑ _u : Unit, subst (F.nthSeries (p ^ 0)) x * 1
        rw [pow_zero]
        simp [hid]
      · intro c hc
        funext u
        rw [pow_zero] at hc
        simp [hid] at hc
        exact hc.symm
    | succ v ih =>
      obtain ⟨ι, _, B, hcard, hB⟩ := ih
      let θ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k :=
        (substAlgHom (hasSubst_of_constantCoeff_zero (h0 (p ^ v)))).toRingHom
      let θ' : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k :=
        (substAlgHom (hasSubst_of_constantCoeff_zero (h0 p))).toRingHom
      have hθ : ∀ x, θ x = subst (F.nthSeries (p ^ v)) x := fun x => by
        show substAlgHom _ x = _; rw [coe_substAlgHom]
      have hθ' : ∀ x, θ' x = subst (F.nthSeries p) x := fun x => by
        show substAlgHom _ x = _; rw [coe_substAlgHom]
      have hB' : ∀ x, ∃! c : ι → MvPowerSeries (Fin d) k, x = ∑ J, θ (c J) * B J := by
        simpa only [hθ] using hB
      have hb' : ∀ x, ∃! c : Fin _ → MvPowerSeries (Fin d) k, x = ∑ j, θ' (c j) * b j := by
        simpa only [hθ'] using hb
      have hc := MvFormalGroup.T1ab.comp_basis θ θ' B b hB' hb'
      refine ⟨ι × Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (F.nthSeries p)))),
        inferInstance, fun q => θ (b q.2) * B q.1, ?_, ?_⟩
      · rw [Fintype.card_prod, Fintype.card_fin, hcard, hh, pow_succ]
      · intro x
        have hcx := hc x
        simp only [hθ, hθ', hcomp] at hcx
        simpa only [hθ] using hcx
  obtain ⟨ι, _, B, hcard, hB⟩ := key v
  rw [MvFormalGroup.T1ab.finrank_quotient_eq_card (h0 (p ^ v)) B hB, hcard, ← pow_mul, mul_comm]

end S_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow (solution)
