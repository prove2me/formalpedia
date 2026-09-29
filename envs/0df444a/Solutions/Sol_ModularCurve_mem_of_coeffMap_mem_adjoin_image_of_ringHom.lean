-- Prove2me | solution 1 for ModularCurve.mem_of_coeffMap_mem_adjoin_image_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a7383c75-04bd-5fd0-b58c-8e1f0e688c8e

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_of_coeffMap_mem_adjoin_image_of_ringHom

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap coeffMap_coeff"
p2m_open "ModularCurve"
namespace CoeffDescent

variable {K L : Type*} [Field K] [Field L] (ι : K →+* L)

omit [Field K] [Field L] in
theorem coeffMap_injective' {K L : Type*} [Field K] [Field L] (ι : K →+* L) :
    Function.Injective (coeffMap ι) := by
  intro x y h
  ext n
  have := congrArg (fun z => HahnSeries.coeff z n) h
  simpa [coeffMap_coeff] using ι.injective this

theorem coeff_finset_sum {M : Type*} (s : Finset M) (f : M → LaurentSeries L) (n : ℤ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem coeff_finset_sumK {M : Type*} (s : Finset M) (f : M → LaurentSeries K) (n : ℤ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

omit [Field K] in
theorem C_eq_algebraMap'' {L : Type*} [Field L] (c : L) : HahnSeries.C c = algebraMap L (LaurentSeries L) c := by
  first
    | rfl
    | exact (HahnSeries.ofPowerSeries_C (Γ := ℤ) (R := L) c).symm

theorem mul_mem_span (F : IntermediateField K (LaurentSeries K)) {a b : LaurentSeries L}
    (ha : a ∈ Submodule.span L (coeffMap ι '' (F : Set (LaurentSeries K))))
    (hb : b ∈ Submodule.span L (coeffMap ι '' (F : Set (LaurentSeries K)))) :
    a * b ∈ Submodule.span L (coeffMap ι '' (F : Set (LaurentSeries K))) := by
  induction ha using Submodule.span_induction with
  | mem u hu =>
    induction hb using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨f, hf, rfl⟩ := hu
      obtain ⟨g, hg, rfl⟩ := hv
      exact Submodule.subset_span ⟨f * g, F.mul_mem hf hg, map_mul _ f g⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add v w _ _ hv hw => rw [mul_add]; exact add_mem hv hw
    | smul c v _ hv =>
      rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul]
      exact Submodule.smul_mem _ c hv
  | zero => rw [zero_mul]; exact zero_mem _
  | add u w _ _ hu hw => rw [add_mul]; exact add_mem hu hw
  | smul c u _ hu =>
    rw [← HahnSeries.C_mul_eq_smul, mul_assoc, HahnSeries.C_mul_eq_smul]
    exact Submodule.smul_mem _ c hu

theorem adjoin_le_span (F : IntermediateField K (LaurentSeries K)) {z : LaurentSeries L}
    (hz : z ∈ Algebra.adjoin L (coeffMap ι '' (F : Set (LaurentSeries K)))) :
    z ∈ Submodule.span L (coeffMap ι '' (F : Set (LaurentSeries K))) := by
  induction hz using Algebra.adjoin_induction with
  | mem u hu => exact Submodule.subset_span hu
  | algebraMap c =>
    have h1 : (1 : LaurentSeries L) ∈ coeffMap ι '' (F : Set (LaurentSeries K)) := ⟨1, F.one_mem, map_one _⟩
    rw [← C_eq_algebraMap'', ← mul_one (HahnSeries.C c), HahnSeries.C_mul_eq_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span h1)
  | add u w _ _ hu hw => exact add_mem hu hw
  | mul u w _ _ hu hw => exact mul_mem_span ι F hu hw

theorem main (F : IntermediateField K (LaurentSeries K)) (x : LaurentSeries K)
    (hx : coeffMap ι x ∈ IntermediateField.adjoin L (coeffMap ι '' (F : Set (LaurentSeries K)))) :
    x ∈ F := by
  classical

  letI : Algebra K L := ι.toAlgebra
  have hsmul : ∀ (k : K) (l : L), k • l = ι k * l := fun k l => rfl

  obtain ⟨r, hr, t, ht, hy⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
  have hr' := (Submodule.mem_span_set').mp (adjoin_le_span ι F hr)
  have ht' := (Submodule.mem_span_set').mp (adjoin_le_span ι F ht)
  obtain ⟨n, c, e, hre⟩ := hr'
  obtain ⟨m, d, e', hte⟩ := ht'

  have hef : ∀ i, ∃ f : LaurentSeries K, f ∈ F ∧ coeffMap ι f = (e i : LaurentSeries L) := fun i => by
    obtain ⟨f, hf, hfe⟩ := (e i).2
    exact ⟨f, hf, hfe⟩
  have heg : ∀ j, ∃ g : LaurentSeries K, g ∈ F ∧ coeffMap ι g = (e' j : LaurentSeries L) := fun j => by
    obtain ⟨g, hg, hge⟩ := (e' j).2
    exact ⟨g, hg, hge⟩
  choose f hfF hfe using hef
  choose g hgF hge using heg

  by_cases ht0 : t = 0
  · rw [ht0, div_zero] at hy
    have hx0 : x = 0 := coeffMap_injective' ι (by rw [hy, map_zero])
    rw [hx0]
    exact zero_mem F

  have hrel : coeffMap ι x * (∑ j, d j • coeffMap ι (g j)) = ∑ i, c i • coeffMap ι (f i) := by
    have h1 : (∑ j, d j • coeffMap ι (g j)) = t := by rw [← hte]; simp_rw [hge]
    have h2 : (∑ i, c i • coeffMap ι (f i)) = r := by rw [← hre]; simp_rw [hfe]
    rw [h1, h2, hy, div_mul_cancel₀ _ ht0]
  let b := Module.Basis.ofVectorSpace K L

  let Gk : Module.Basis.ofVectorSpaceIndex K L → LaurentSeries K := fun k => ∑ j, (b.repr (d j) k) • g j
  let Fk : Module.Basis.ofVectorSpaceIndex K L → LaurentSeries K := fun k => ∑ i, (b.repr (c i) k) • f i
  have hCmem : ∀ r : K, HahnSeries.C r ∈ F := fun r => by
    rw [C_eq_algebraMap'']; exact F.algebraMap_mem r
  have hGk : ∀ k, Gk k ∈ F := fun k => sum_mem fun j _ => by
    rw [← HahnSeries.C_mul_eq_smul]; exact F.mul_mem (hCmem _) (hgF j)
  have hFk : ∀ k, Fk k ∈ F := fun k => sum_mem fun i _ => by
    rw [← HahnSeries.C_mul_eq_smul]; exact F.mul_mem (hCmem _) (hfF i)

  have hxG : ∀ k, x * Gk k = Fk k := by
    intro k
    ext N

    have hN := congrArg (fun z : LaurentSeries L => z.coeff N) hrel
    simp only [Finset.mul_sum, coeff_finset_sum, HahnSeries.coeff_smul, smul_eq_mul] at hN

    have hL : ∀ j, (coeffMap ι x * (d j • coeffMap ι (g j))).coeff N = d j * ι ((x * g j).coeff N) := by
      intro j
      rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        smul_eq_mul, ← map_mul, coeffMap_coeff]
    simp only [hL, coeffMap_coeff] at hN

    have hN' : ∑ j, ((x * g j).coeff N) • d j = ∑ i, ((f i).coeff N) • c i := by
      simp only [hsmul]
      simpa [mul_comm] using hN
    have hk := congrArg (fun l : L => b.repr l k) hN'
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul] at hk

    simp only [Gk, Fk, Finset.mul_sum, coeff_finset_sumK]
    have e1 : ∀ j, (x * ((b.repr (d j)) k • g j)).coeff N = (x * g j).coeff N * (b.repr (d j)) k := by
      intro j
      rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        smul_eq_mul, mul_comm]
    have e2 : ∀ i, (((b.repr (c i)) k) • f i).coeff N = (f i).coeff N * (b.repr (c i)) k := by
      intro i
      rw [HahnSeries.coeff_smul, smul_eq_mul, mul_comm]
    simp only [e1, e2]
    exact hk

  have hex : ∃ k, Gk k ≠ 0 := by
    by_contra hall
    push Not at hall
    apply ht0
    rw [← hte]
    simp_rw [← hge]

    let S := (Finset.univ : Finset (Fin m)).biUnion fun j => (b.repr (d j)).support
    have hd : ∀ j, d j = ∑ k ∈ S, (b.repr (d j) k) • b k := by
      intro j
      conv_lhs => rw [← b.linearCombination_repr (d j)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun j => (b.repr (d j)).support)
          (Finset.mem_univ j)) _ (by simp)]
    calc ∑ j, d j • coeffMap ι (g j)
        = ∑ j, ∑ k ∈ S, (b k) • ((b.repr (d j) k) • coeffMap ι (g j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          nth_rewrite 1 [hd j]
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsmul, mul_comm, mul_smul]
          rfl
      _ = ∑ k ∈ S, (b k) • coeffMap ι (Gk k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.smul_sum]
          congr 1
          simp only [Gk, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_

          ext N
          simp [coeffMap_coeff, HahnSeries.coeff_smul, hsmul]
      _ = 0 := by simp [hall]
  obtain ⟨k, hk⟩ := hex
  have hxeq : x = Fk k / Gk k := by rw [← hxG k, mul_div_cancel_right₀ _ hk]
  rw [hxeq]
  exact div_mem (hFk k) (hGk k)

end CoeffDescent
end ModularCurve

end

theorem solution
    {K L : Type*} [Field K] [Field L] (ι : K →+* L) (F : IntermediateField K (LaurentSeries K))
    (x : LaurentSeries K)
    (hx : ModularCurve.coeffMap ι x ∈
      IntermediateField.adjoin L (ModularCurve.coeffMap ι '' (F : Set (LaurentSeries K)))) :
    x ∈ F :=
  ModularCurve.CoeffDescent.main ι F x hx

end S_ModularCurve_mem_of_coeffMap_mem_adjoin_image_of_ringHom
end P2MW
export P2MW.S_ModularCurve_mem_of_coeffMap_mem_adjoin_image_of_ringHom (solution)
