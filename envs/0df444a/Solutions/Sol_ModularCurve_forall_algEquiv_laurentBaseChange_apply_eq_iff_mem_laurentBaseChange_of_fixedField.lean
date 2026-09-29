-- Prove2me | solution 1 for ModularCurve.forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9ee2dbda-aae1-57f5-9d61-5ed303562f1e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace FixedLBC

open ModularCurve

theorem coeff_algebraMap_mul_coeffEmb (L : Type) [Field L] [CharZero L]
    (b : L) (v : LaurentSeries ℚ) (n : ℤ) :
    (algebraMap L (LaurentSeries L) b * coeffEmb L v).coeff n = (v.coeff n) • b := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul,
    coeffEmb_coeff, smul_eq_mul, Algebra.smul_def, mul_comm]

theorem eq_of_sum_eq (L : Type) [Field L] [CharZero L]
    {κ : Type} (B : κ → L) (hB : LinearIndependent ℚ B) (S : Finset κ)
    (u u' : κ → LaurentSeries ℚ)
    (h : ∑ k ∈ S, algebraMap L (LaurentSeries L) (B k) * coeffEmb L (u k) =
      ∑ k ∈ S, algebraMap L (LaurentSeries L) (B k) * coeffEmb L (u' k)) :
    ∀ k ∈ S, u k = u' k := by
  intro k hk
  refine HahnSeries.coeff_injective (funext fun n => ?_)
  have hn := congrArg (fun x : LaurentSeries L => x.coeff n) h
  simp only [HahnSeries.coeff_sum, coeff_algebraMap_mul_coeffEmb] at hn
  have h0 : ∑ k ∈ S, ((u k).coeff n - (u' k).coeff n) • B k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hn, sub_self]
  exact sub_eq_zero.mp (linearIndependent_iff'.mp hB S _ h0 k hk)

theorem sum_eq_sum_basis (L : Type) [Field L] [CharZero L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    {κ : Type} (B : Module.Basis κ ℚ L)
    {I : Type} (T : Finset I) (c : I → L) (f : I → ↥F₀) (S : Finset κ)
    (hS : ∀ i ∈ T, (B.repr (c i)).support ⊆ S) :
    ∑ i ∈ T, algebraMap L (LaurentSeries L) (c i) * coeffEmb L (f i : LaurentSeries ℚ) =
      ∑ k ∈ S, algebraMap L (LaurentSeries L) (B k) *
        coeffEmb L ((∑ i ∈ T, ((B.repr (c i) k : ℚ) : ↥F₀) * f i : ↥F₀) : LaurentSeries ℚ) := by
  classical
  have hc : ∀ i ∈ T, c i = ∑ k ∈ S, (B.repr (c i) k) • B k := by
    intro i hi
    conv_lhs => rw [← B.linearCombination_repr (c i)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hS i hi)]
    intro k _; exact zero_smul _ _
  have hq : ∀ (q : ℚ) (y : ↥F₀), coeffEmb L (((q : ↥F₀) * y : ↥F₀) : LaurentSeries ℚ) =
      (q : LaurentSeries L) * coeffEmb L (y : LaurentSeries ℚ) := by
    intro q y
    rw [MulMemClass.coe_mul, SubfieldClass.coe_ratCast, map_mul, map_ratCast]
  have hq' : ∀ (q : ℚ) (b : L), algebraMap L (LaurentSeries L) (q • b) =
      (q : LaurentSeries L) * algebraMap L (LaurentSeries L) b := by
    intro q b
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact eq_ratCast ((algebraMap L (LaurentSeries L)).comp (algebraMap ℚ L)) q
  calc ∑ i ∈ T, algebraMap L (LaurentSeries L) (c i) * coeffEmb L (f i : LaurentSeries ℚ)
      = ∑ i ∈ T, ∑ k ∈ S, algebraMap L (LaurentSeries L) ((B.repr (c i) k) • B k) *
          coeffEmb L (f i : LaurentSeries ℚ) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        conv_lhs => rw [hc i hi, map_sum, Finset.sum_mul]
    _ = ∑ k ∈ S, ∑ i ∈ T, algebraMap L (LaurentSeries L) ((B.repr (c i) k) • B k) *
          coeffEmb L (f i : LaurentSeries ℚ) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hq, hq']
        ring

theorem sum_mem_of_fixed (L : Type) [Field L] [CharZero L]
    (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    (G : Type) [Group G] (δ : G →* (↥F₀ ≃ₐ[ℚ] ↥F₀))
    (hF₁ : ∀ y : ↥F₀, (y : LaurentSeries ℚ) ∈ F₁ ↔ ∀ g : G, δ g y = y)
    {I : Type} (T : Finset I) (c : I → L) (f : I → ↥F₀)
    (hfix : ∀ g : G, ∑ i ∈ T, algebraMap L (LaurentSeries L) (c i) * coeffEmb L ((δ g (f i) : ↥F₀) : LaurentSeries ℚ) =
      ∑ i ∈ T, algebraMap L (LaurentSeries L) (c i) * coeffEmb L (f i : LaurentSeries ℚ)) :
    ∑ i ∈ T, algebraMap L (LaurentSeries L) (c i) * coeffEmb L (f i : LaurentSeries ℚ) ∈
      laurentBaseChange L F₁ := by
  classical
  let B := Module.Free.chooseBasis ℚ L
  let S : Finset (Module.Free.ChooseBasisIndex ℚ L) := T.biUnion fun i => (B.repr (c i)).support
  have hS : ∀ i ∈ T, (B.repr (c i)).support ⊆ S := fun i hi =>
    Finset.subset_biUnion_of_mem (fun i => (B.repr (c i)).support) hi
  let w : Module.Free.ChooseBasisIndex ℚ L → ↥F₀ := fun k => ∑ i ∈ T, ((B.repr (c i) k : ℚ) : ↥F₀) * f i
  have hrep := sum_eq_sum_basis L F₀ B T c f S hS
  rw [hrep]
  have hw : ∀ k ∈ S, (w k : LaurentSeries ℚ) ∈ F₁ := by
    intro k hk
    refine (hF₁ (w k)).mpr fun g => ?_
    have hrepg := sum_eq_sum_basis L F₀ B T c (fun i => δ g (f i)) S hS
    have hwg : ∀ k, (∑ i ∈ T, ((B.repr (c i) k : ℚ) : ↥F₀) * δ g (f i) : ↥F₀) = δ g (w k) := by
      intro k
      simp only [w, map_sum, map_mul, map_ratCast]
    simp only [hwg] at hrepg
    have hfixg := hfix g
    rw [hrep, hrepg] at hfixg
    have := eq_of_sum_eq L B B.linearIndependent S (fun k => ((δ g (w k) : ↥F₀) : LaurentSeries ℚ))
      (fun k => (w k : LaurentSeries ℚ)) hfixg k hk
    exact Subtype.ext this
  refine sum_mem fun k hk => mul_mem ((laurentBaseChange L F₁).algebraMap_mem _) ?_
  exact coeffEmb_mem_laurentBaseChange L (hw k hk)

section K

variable (L : Type) [Field L] [CharZero L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

def ι (y : ↥F₀) : ↥(laurentBaseChange L F₀) := ⟨coeffEmb L (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L y.2⟩

@[scoped simp] theorem coe_ι (y : ↥F₀) : (ι L F₀ y : LaurentSeries L) = coeffEmb L (y : LaurentSeries ℚ) := rfl

def ιMon : Submonoid ↥(laurentBaseChange L F₀) where
  carrier := Set.range (ι L F₀)
  mul_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
    exact ⟨y * y', Subtype.ext (by simp)⟩
  one_mem' := ⟨1, Subtype.ext (by simp)⟩

theorem exists_finsupp_of_mem_A {z : ↥(laurentBaseChange L F₀)}
    (hz : z ∈ Algebra.adjoin L (Set.range (ι L F₀))) :
    ∃ c : ↥F₀ →₀ L, z = ∑ y ∈ c.support, c y • ι L F₀ y := by
  have hcl : Submonoid.closure (Set.range (ι L F₀)) = ιMon L F₀ := Submonoid.closure_eq (ιMon L F₀)
  have h := Algebra.adjoin_eq_span_of_subset (R := L) (s := Set.range (ι L F₀))
    (by rw [hcl]; exact Submodule.subset_span)
  have hz' : z ∈ Submodule.span L (Set.range (ι L F₀)) := by
    rw [← h]; exact hz
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz'
  obtain ⟨c, hc⟩ := hz'
  exact ⟨c, hc.symm⟩

theorem exists_div (x : ↥(laurentBaseChange L F₀)) :
    ∃ r ∈ Algebra.adjoin L (Set.range (ι L F₀)), ∃ s ∈ Algebra.adjoin L (Set.range (ι L F₀)), x = r / s := by
  have hx : (x : LaurentSeries L) ∈ IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) := x.2
  rw [IntermediateField.mem_adjoin_iff_div] at hx
  obtain ⟨r, hr, s, hs, hrs⟩ := hx
  have himg : ⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)) =
      (laurentBaseChange L F₀).val '' Set.range (ι L F₀) := by
    ext v
    simp only [Set.mem_image, Set.mem_range, SetLike.mem_coe, IntermediateField.coe_val]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨ι L F₀ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, y.2, rfl⟩
  have hmap : Algebra.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) =
      (Algebra.adjoin L (Set.range (ι L F₀))).map (laurentBaseChange L F₀).val := by
    rw [himg]
    exact Algebra.adjoin_image (R := L) (laurentBaseChange L F₀).val (Set.range (ι L F₀))
  rw [hmap, Subalgebra.mem_map] at hr hs
  obtain ⟨r', hr', rfl⟩ := hr
  obtain ⟨s', hs', rfl⟩ := hs
  refine ⟨r', hr', s', hs', Subtype.ext ?_⟩
  rw [hrs, IntermediateField.coe_div]
  rfl

end K

end FixedLBC
p2m_reactivate "P2MW.S_ModularCurve_forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField.FixedLBC"

end
p2m_reactivate "P2MW.S_ModularCurve_forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField.FixedLBC"

open ModularCurve in

theorem solution
    (L : Type) [Field L] [CharZero L]
    (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)) (hle₁ : F₁ ≤ F₀)
    (G : Type) [Group G] [Finite G] (δ : G →* (↥F₀ ≃ₐ[ℚ] ↥F₀))
    (hF₁ : ∀ y : ↥F₀, (y : LaurentSeries ℚ) ∈ F₁ ↔ ∀ g : G, δ g y = y)
    (δL : G →* (↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀)))
    (hδL : ∀ (g : G) (y : ↥F₀) (hy : ModularCurve.coeffEmb L (y : LaurentSeries ℚ) ∈ ModularCurve.laurentBaseChange L F₀),
      ((δL g ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ), hy⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) =
        ModularCurve.coeffEmb L ((δ g y : ↥F₀) : LaurentSeries ℚ))
    (x : ↥(ModularCurve.laurentBaseChange L F₀)) :
    (∀ g : G, δL g x = x) ↔ (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L F₁ := by
  classical
  have hι : ∀ (g : G) (y : ↥F₀), δL g (FixedLBC.ι L F₀ y) = FixedLBC.ι L F₀ (δ g y) := fun g y =>
    Subtype.ext (hδL g y _)
  have hsm : ∀ (g : G) (a : L) (z : ↥(laurentBaseChange L F₀)), δL g (a • z) = a • δL g z := fun g a z =>
    (δL g).toLinearEquiv.map_smul a z

  have hA : ∀ (g : G) {z : ↥(laurentBaseChange L F₀)}, z ∈ Algebra.adjoin L (Set.range (FixedLBC.ι L F₀)) → δL g z ∈ Algebra.adjoin L (Set.range (FixedLBC.ι L F₀)) := by
    intro g z hz
    have hle : Algebra.adjoin L (Set.range (FixedLBC.ι L F₀)) ≤ (Algebra.adjoin L (Set.range (FixedLBC.ι L F₀))).comap (δL g).toAlgHom := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨y, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_comap, AlgEquiv.toAlgHom_apply, hι]
      exact Algebra.subset_adjoin ⟨_, rfl⟩
    exact (Subalgebra.mem_comap _ _ _).mp (hle hz)

  have hfixA : ∀ {z : ↥(laurentBaseChange L F₀)}, z ∈ Algebra.adjoin L (Set.range (FixedLBC.ι L F₀)) → (∀ g : G, δL g z = z) →
      (z : LaurentSeries L) ∈ laurentBaseChange L F₁ := by
    intro z hz hfz
    obtain ⟨c, rfl⟩ := FixedLBC.exists_finsupp_of_mem_A L F₀ hz
    have hval : ∀ (f : ↥F₀ → ↥F₀),
        ((∑ y ∈ c.support, c y • FixedLBC.ι L F₀ (f y) : ↥(laurentBaseChange L F₀)) : LaurentSeries L) =
        ∑ y ∈ c.support, algebraMap L (LaurentSeries L) (c y) * coeffEmb L ((f y : ↥F₀) : LaurentSeries ℚ) := by
      intro f
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [IntermediateField.coe_smul, Algebra.smul_def, FixedLBC.coe_ι]
    have hid := hval id
    simp only [id] at hid
    rw [hid]
    refine FixedLBC.sum_mem_of_fixed L F₀ F₁ G δ hF₁ c.support (fun y => c y) (fun y => y) fun g => ?_
    have hg := congrArg (fun t : ↥(laurentBaseChange L F₀) => (t : LaurentSeries L)) (hfz g)
    simp only [map_sum, hsm, hι] at hg
    rw [hval (fun y => δ g y), hid] at hg
    exact hg
  constructor
  ·
    intro hx
    letI : Fintype G := Fintype.ofFinite G
    obtain ⟨r, hr, s, hs, hxrs⟩ := FixedLBC.exists_div L F₀ x
    by_cases hs0 : s = 0
    · rw [hxrs, hs0, div_zero, ZeroMemClass.coe_zero]; exact zero_mem _
    obtain ⟨Nf, hNf⟩ : ∃ Nf : ↥(laurentBaseChange L F₀), Nf = ∏ g, δL g s := ⟨_, rfl⟩
    have hNfA : Nf ∈ Algebra.adjoin L (Set.range (FixedLBC.ι L F₀)) := by
      rw [hNf]; exact Subalgebra.prod_mem _ fun g _ => hA g hs
    have hNf0 : Nf ≠ 0 := by
      rw [hNf]
      exact Finset.prod_ne_zero_iff.mpr fun g _ => (map_ne_zero_iff (δL g) (δL g).injective).mpr hs0
    have hNfix : ∀ h : G, δL h Nf = Nf := by
      intro h
      rw [hNf, map_prod]
      exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ fun g => by
        simp only [Equiv.coe_mulLeft, map_mul, AlgEquiv.mul_apply]
    have hP : Nf = s * ∏ g ∈ Finset.univ.erase 1, δL g s := by
      rw [hNf, ← Finset.mul_prod_erase Finset.univ (fun g => δL g s) (Finset.mem_univ 1), map_one,
        AlgEquiv.one_apply]
    have haA : x * Nf ∈ Algebra.adjoin L (Set.range (FixedLBC.ι L F₀)) := by
      rw [hP, hxrs, ← mul_assoc, div_mul_cancel₀ r hs0]
      exact mul_mem hr (Subalgebra.prod_mem _ fun g _ => hA g hs)
    have hafix : ∀ g : G, δL g (x * Nf) = x * Nf := fun g => by rw [map_mul, hx g, hNfix g]
    have hxeq : x = (x * Nf) / Nf := (eq_div_iff hNf0).mpr rfl
    have ha := hfixA haA hafix
    have hN := hfixA hNfA hNfix
    rw [hxeq, IntermediateField.coe_div]
    exact div_mem ha hN
  ·
    intro hx
    have hle : laurentBaseChange L F₁ ≤
        (IntermediateField.fixedField δL.range).map (laurentBaseChange L F₀).val := by
      change IntermediateField.adjoin L _ ≤ _
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, hy, rfl⟩
      refine (IntermediateField.mem_map _).mpr ⟨FixedLBC.ι L F₀ ⟨y, hle₁ hy⟩, ?_, rfl⟩
      refine (IntermediateField.mem_fixedField_iff _ _).mpr ?_
      rintro _ ⟨g, rfl⟩
      rw [hι]
      congr 1
      exact (hF₁ ⟨y, hle₁ hy⟩).mp hy g
    obtain ⟨z, hz, hzx⟩ := (IntermediateField.mem_map _).mp (hle hx)
    have hzx' : z = x := Subtype.ext hzx
    subst hzx'
    intro g
    exact (IntermediateField.mem_fixedField_iff _ _).mp hz _ ⟨g, rfl⟩

#print axioms solution

end S_ModularCurve_forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField
end P2MW
export P2MW.S_ModularCurve_forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField (solution)
