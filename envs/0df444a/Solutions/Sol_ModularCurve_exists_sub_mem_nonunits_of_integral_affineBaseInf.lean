-- Prove2me | solution 1 for ModularCurve.exists_sub_mem_nonunits_of_integral_affineBaseInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/33094ff9-b990-5664-a9cd-04ca2019aacf

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord exists_unit_mul_zpow algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem (a : K) : algebraMap K F a ∈ w.toValuationSubring :=
    w.algebraMap_mem' a

p2m_export "AlgebraicCurve.Place" "algebraMap_mem"
private theorem _root_.AlgebraicCurve.Place.algebraMap_mem_nonunits_iff (a : K) :
    algebraMap K F a ∈ w.toValuationSubring.nonunits ↔ a = 0 := by
  constructor
  · intro h
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp h with h0 | hinv
    · exact (map_eq_zero _).mp h0
    · exact absurd (by simpa using w.algebraMap_mem a⁻¹) hinv
  · rintro rfl
    simp [ZeroMemClass.zero_mem]

p2m_export "AlgebraicCurve.Place" "algebraMap_mem_nonunits_iff"
private theorem _root_.AlgebraicCurve.Place.mul_mem_nonunits {x y : F} (hx : x ∈ w.toValuationSubring.nonunits)
    (hy : y ∈ w.toValuationSubring) : x * y ∈ w.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  calc w.toValuationSubring.valuation (x * y)
      = w.toValuationSubring.valuation x * w.toValuationSubring.valuation y := map_mul _ _ _
    _ ≤ w.toValuationSubring.valuation x * 1 := by gcongr
    _ = w.toValuationSubring.valuation x := mul_one _
    _ < 1 := hx

p2m_export "AlgebraicCurve.Place" "mul_mem_nonunits"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_pos {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_pos"
private theorem _root_.AlgebraicCurve.Place.mem_nonunits_iff_ord_pos {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.nonunits ↔ 0 < w.ord f := by
  constructor
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.mem_of_ord_pos h
    have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'

p2m_export "AlgebraicCurve.Place" "mem_nonunits_iff_ord_pos"
private def _root_.AlgebraicCurve.Place.HasValueAt (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ w.toValuationSubring.nonunits

p2m_export "AlgebraicCurve.Place" "HasValueAt"
theorem hasValueAt_iff (f : F) (a : K) :
    w.HasValueAt f a ↔ f - algebraMap K F a ∈ w.toValuationSubring.nonunits := Iff.rfl

private theorem _root_.AlgebraicCurve.Place.hasValueAt_iff_ord_pos {f : F} {a : K} (h : f ≠ algebraMap K F a) :
    w.HasValueAt f a ↔ 0 < w.ord (f - algebraMap K F a) :=
  w.mem_nonunits_iff_ord_pos (sub_ne_zero.mpr h)

p2m_export "AlgebraicCurve.Place" "hasValueAt_iff_ord_pos"
private theorem _root_.AlgebraicCurve.Place.hasValueAt_of_ord_pos {f : F} {a : K} (h : 0 < w.ord (f - algebraMap K F a)) :
    w.HasValueAt f a := by
  have hne : f ≠ algebraMap K F a := by
    intro hfa; rw [hfa, sub_self] at h; simp at h
  exact (w.hasValueAt_iff_ord_pos hne).mpr h

p2m_export "AlgebraicCurve.Place" "hasValueAt_of_ord_pos"
private theorem _root_.AlgebraicCurve.Place.hasValueAt_algebraMap (a : K) : w.HasValueAt (algebraMap K F a) a := by
  simp [HasValueAt, ZeroMemClass.zero_mem]

p2m_export "AlgebraicCurve.Place" "hasValueAt_algebraMap"
private theorem _root_.AlgebraicCurve.Place.hasValueAt_zero_iff (f : F) : w.HasValueAt f 0 ↔ f ∈ w.toValuationSubring.nonunits
    := by
  simp [HasValueAt]

p2m_export "AlgebraicCurve.Place" "hasValueAt_zero_iff"
private theorem _root_.AlgebraicCurve.Place.mem_of_hasValueAt {f : F} {a : K} (h : w.HasValueAt f a) : f ∈ w.toValuationSubring
    := by
  have h1 : f - algebraMap K F a ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
  simpa using add_mem h1 (w.algebraMap_mem a)

p2m_export "AlgebraicCurve.Place" "mem_of_hasValueAt"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.unique {f : F} {a b : K} (ha : w.HasValueAt f a) (hb : w.HasValueAt f b)
    :
    a = b := by
  have h : algebraMap K F (a - b) ∈ w.toValuationSubring.nonunits := by
    have := sub_mem hb ha
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  exact sub_eq_zero.mp ((w.algebraMap_mem_nonunits_iff _).mp h)

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.unique"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.add {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f + g) (a + b) := by
  have := add_mem hf hg
  rw [HasValueAt, map_add]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.add"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.neg {f : F} {a : K} (hf : w.HasValueAt f a) : w.HasValueAt (-f) (-a) :=
    by
  have := neg_mem hf
  rw [HasValueAt, map_neg]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.neg"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.mul {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f * g) (a * b) := by
  have h1 : (f - algebraMap K F a) * g ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (w.mem_of_hasValueAt hg)
  have h2 : (g - algebraMap K F b) * algebraMap K F a ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hg (w.algebraMap_mem a)
  have := add_mem h1 h2
  rw [HasValueAt, map_mul]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.mul"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.inv {f : F} {a : K} (hf : w.HasValueAt f a) (ha : a ≠ 0) :
    w.HasValueAt f⁻¹ a⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : w.HasValueAt (0 : F) 0 := by simpa using w.hasValueAt_algebraMap 0
    exact ha (hf.unique this)
  have hfu : f ∉ w.toValuationSubring.nonunits := fun hfn =>
    ha (hf.unique ((w.hasValueAt_zero_iff f).mpr hfn))
  have hfinv : f⁻¹ ∈ w.toValuationSubring := by
    by_contra hne
    exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
  have hprod : (f - algebraMap K F a) * (f⁻¹ * algebraMap K F a⁻¹)
      ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (mul_mem hfinv (w.algebraMap_mem _))
  have := neg_mem hprod
  change f⁻¹ - algebraMap K F a⁻¹ ∈ w.toValuationSubring.nonunits
  convert this using 1
  have haF : algebraMap K F a ≠ 0 := by simpa using ha
  rw [map_inv₀]
  field_simp
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.inv"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.div {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b)
    (hb : b ≠ 0) : w.HasValueAt (f / g) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hf.mul (hg.inv hb)

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.div"
private theorem _root_.AlgebraicCurve.Place.hasValueAt_iff_residue {f : F} (hf : f ∈ w.toValuationSubring) (a : K) :
    w.HasValueAt f a ↔
      residue w.toValuationSubring ⟨f, hf⟩ = algebraMap K w.ResidueField a := by
  have e : algebraMap K w.ResidueField a =
      residue w.toValuationSubring (algebraMap K w.toValuationSubring a) := rfl
  rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

p2m_export "AlgebraicCurve.Place" "hasValueAt_iff_residue"
private theorem _root_.AlgebraicCurve.Place.exists_hasValueAt (hw : Function.Surjective (algebraMap K w.ResidueField)) {f : F}
    (hf : f ∈ w.toValuationSubring) : ∃ a : K, w.HasValueAt f a := by
  obtain ⟨a, ha⟩ := hw (residue w.toValuationSubring ⟨f, hf⟩)
  exact ⟨a, (w.hasValueAt_iff_residue hf a).mpr ha.symm⟩

p2m_export "AlgebraicCurve.Place" "exists_hasValueAt"
private theorem _root_.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed [IsAlgClosed K]
    [Module.Finite K w.ResidueField] : Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K w.ResidueField
  (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

p2m_export "AlgebraicCurve.Place" "surjective_algebraMap_residueField_of_isAlgClosed"
theorem surjective_algebraMap_residueField_of_deg_eq_one [IsAlgClosed K] (h : w.deg = 1) :
    Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Module.Finite K w.ResidueField := Module.finite_of_finrank_eq_succ (n := 0) h
  w.surjective_algebraMap_residueField_of_isAlgClosed

variable (A : ValuationSubring K)

private def _root_.AlgebraicCurve.Place.compSubring : Subring F where
  carrier := {f | ∃ a : A, w.HasValueAt f a}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simpa using ha.mul hb⟩
  one_mem' := ⟨1, by simpa using w.hasValueAt_algebraMap 1⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using ha.add hb⟩
  zero_mem' := ⟨0, by simpa using w.hasValueAt_algebraMap 0⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨-a, by simpa using ha.neg⟩

p2m_export "AlgebraicCurve.Place" "compSubring"
variable {A} in
private theorem _root_.AlgebraicCurve.Place.mem_compSubring_iff {f : F} : f ∈ w.compSubring A ↔ ∃ a : A, w.HasValueAt f a :=
  Iff.rfl

p2m_export "AlgebraicCurve.Place" "mem_compSubring_iff"
variable {A} in
private theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_hasValueAt {f : F} {a : K} (ha : a ∈ A) (h : w.HasValueAt f a) :
    f ∈ w.compSubring A :=
  ⟨⟨a, ha⟩, h⟩

p2m_export "AlgebraicCurve.Place" "mem_compSubring_of_hasValueAt"
private theorem _root_.AlgebraicCurve.Place.compSubring_le : w.compSubring A ≤ w.toValuationSubring.toSubring := by
  rintro f ⟨a, ha⟩
  exact w.mem_of_hasValueAt ha

p2m_export "AlgebraicCurve.Place" "compSubring_le"
private theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_mem_nonunits {f : F} (hf : f ∈ w.toValuationSubring.nonunits) :
    f ∈ w.compSubring A :=
  ⟨0, by simpa [w.hasValueAt_zero_iff] using hf⟩

p2m_export "AlgebraicCurve.Place" "mem_compSubring_of_mem_nonunits"
private theorem _root_.AlgebraicCurve.Place.algebraMap_mem_compSubring_iff (a : K) : algebraMap K F a ∈ w.compSubring A ↔ a ∈ A
    := by
  constructor
  · rintro ⟨b, hb⟩
    rw [(w.hasValueAt_algebraMap a).unique hb]
    exact b.2
  · intro ha
    exact ⟨⟨a, ha⟩, w.hasValueAt_algebraMap a⟩

p2m_export "AlgebraicCurve.Place" "algebraMap_mem_compSubring_iff"
private def _root_.AlgebraicCurve.Place.value : w.compSubring A →+* A where
  toFun f := Classical.choose f.2
  map_one' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).one_mem).unique (by
      simpa using w.hasValueAt_algebraMap 1)
  map_mul' f g := Subtype.ext <|
    (Classical.choose_spec (mul_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).mul (Classical.choose_spec g.2))
  map_zero' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).zero_mem).unique (by
      simpa using w.hasValueAt_algebraMap 0)
  map_add' f g := Subtype.ext <|
    (Classical.choose_spec (add_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).add (Classical.choose_spec g.2))

p2m_export "AlgebraicCurve.Place" "value"
private theorem _root_.AlgebraicCurve.Place.hasValueAt_value (f : w.compSubring A) : w.HasValueAt (f : F) (w.value A f : K) :=
  Classical.choose_spec f.2

p2m_export "AlgebraicCurve.Place" "hasValueAt_value"
variable {A} in
private theorem _root_.AlgebraicCurve.Place.value_eq_of_hasValueAt {f : w.compSubring A} {a : A} (h : w.HasValueAt (f : F) a) :
    w.value A f = a :=
  Subtype.ext ((w.hasValueAt_value A f).unique h)

p2m_export "AlgebraicCurve.Place" "value_eq_of_hasValueAt"
variable {A} in
theorem ord_sub_value_pos {f : w.compSubring A} (hf : (f : F) ≠ algebraMap K F (w.value A
    f)) :
    0 < w.ord ((f : F) - algebraMap K F (w.value A f)) :=
  (w.hasValueAt_iff_ord_pos hf).mp (w.hasValueAt_value A f)

variable {A} in
theorem value_eq_of_ord_pos {f : w.compSubring A} {a : A}
    (h : 0 < w.ord ((f : F) - algebraMap K F a)) : w.value A f = a :=
  w.value_eq_of_hasValueAt (w.hasValueAt_of_ord_pos h)

private theorem _root_.AlgebraicCurve.Place.value_algebraMap (a : A) :
    w.value A ⟨algebraMap K F a, (w.algebraMap_mem_compSubring_iff A a).mpr a.2⟩ = a :=
  w.value_eq_of_hasValueAt (w.hasValueAt_algebraMap (a : K))

p2m_export "AlgebraicCurve.Place" "value_algebraMap"
private theorem _root_.AlgebraicCurve.Place.value_surjective : Function.Surjective (w.value A) :=
  fun a => ⟨_, w.value_algebraMap A a⟩

p2m_export "AlgebraicCurve.Place" "value_surjective"
variable {A} in
private theorem _root_.AlgebraicCurve.Place.value_eq_zero_of_mem_nonunits {f : w.compSubring A}
    (hf : (f : F) ∈ w.toValuationSubring.nonunits) : w.value A f = 0 :=
  w.value_eq_of_hasValueAt (by simpa [w.hasValueAt_zero_iff] using hf)

p2m_export "AlgebraicCurve.Place" "value_eq_zero_of_mem_nonunits"
private def _root_.AlgebraicCurve.Place.centre : Ideal (w.compSubring A) := (maximalIdeal A).comap (w.value A)

p2m_export "AlgebraicCurve.Place" "centre"
scoped instance centre_isPrime : (w.centre A).IsPrime := Ideal.comap_isPrime _ _

scoped instance centre_isMaximal : (w.centre A).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (w.value_surjective A)

variable {A} in
theorem mem_centre_iff (f : w.compSubring A) : f ∈ w.centre A ↔ w.value A f ∈ maximalIdeal A
    :=
  Iff.rfl

variable {A} in
private theorem _root_.AlgebraicCurve.Place.mem_centre_iff_of_hasValueAt {f : w.compSubring A} {a : A} (h : w.HasValueAt (f : F)
    a) :
    f ∈ w.centre A ↔ a ∈ maximalIdeal A := by
  rw [mem_centre_iff, w.value_eq_of_hasValueAt h]

p2m_export "AlgebraicCurve.Place" "mem_centre_iff_of_hasValueAt"
variable {A} in
theorem mem_centre_iff_of_ord_pos {f : w.compSubring A} {a : A}
    (h : 0 < w.ord ((f : F) - algebraMap K F a)) : f ∈ w.centre A ↔ a ∈ maximalIdeal A :=
  w.mem_centre_iff_of_hasValueAt (w.hasValueAt_of_ord_pos h)

variable {A} in
private theorem _root_.AlgebraicCurve.Place.mem_centre_of_mem_nonunits {f : w.compSubring A}
    (hf : (f : F) ∈ w.toValuationSubring.nonunits) : f ∈ w.centre A := by
  rw [mem_centre_iff, w.value_eq_zero_of_mem_nonunits hf]
  exact Ideal.zero_mem _

p2m_export "AlgebraicCurve.Place" "mem_centre_of_mem_nonunits"
variable {A} in
theorem mem_centre_of_ord_pos {f : w.compSubring A} (hf : 0 < w.ord (f : F)) : f ∈ w.centre
    A :=
  w.mem_centre_of_mem_nonunits ((w.mem_nonunits_iff_ord_pos (by rintro h; simp [h] at hf)).mpr hf)

theorem algebraMap_mem_centre_iff (a : A) :
    (⟨algebraMap K F a, (w.algebraMap_mem_compSubring_iff A a).mpr a.2⟩ : w.compSubring A)
        ∈ w.centre A ↔ a ∈ maximalIdeal A := by
  rw [mem_centre_iff, value_algebraMap]

private theorem _root_.AlgebraicCurve.Place.mem_compSubring_or_inv_mem (hw : Function.Surjective (algebraMap K w.ResidueField))
    (f : F) : f ∈ w.compSubring A ∨ f⁻¹ ∈ w.compSubring A := by
  by_cases hf : f ∈ w.toValuationSubring
  · obtain ⟨c, hc⟩ := w.exists_hasValueAt hw hf
    by_cases hcA : c ∈ A
    · exact Or.inl ⟨⟨c, hcA⟩, hc⟩
    · right
      have hcA' : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
      have hc0 : c ≠ 0 := fun h => hcA (h ▸ A.zero_mem)
      have hf0 : f ≠ 0 := by
        rintro rfl
        have : w.HasValueAt (0 : F) 0 := by simpa using w.hasValueAt_algebraMap 0
        exact hc0 (hc.unique this)
      have hfu : f ∉ w.toValuationSubring.nonunits := by
        intro hfn
        exact hc0 (hc.unique ((w.hasValueAt_zero_iff f).mpr hfn))
      have hfinv : f⁻¹ ∈ w.toValuationSubring := by
        by_contra hne
        exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
      refine ⟨⟨c⁻¹, hcA'⟩, ?_⟩
      have hprod : (f - algebraMap K F c) * (f⁻¹ * algebraMap K F c⁻¹)
          ∈ w.toValuationSubring.nonunits :=
        w.mul_mem_nonunits hc (mul_mem hfinv (w.algebraMap_mem _))
      have := neg_mem hprod
      show f⁻¹ - algebraMap K F (c⁻¹ : K) ∈ w.toValuationSubring.nonunits
      convert this using 1
      have hcF : algebraMap K F c ≠ 0 := by simpa using hc0
      rw [map_inv₀]
      field_simp
      ring
  ·
    right
    refine w.mem_compSubring_of_mem_nonunits A ?_
    exact (ValuationSubring.inv_mem_nonunits_iff _).mpr (Or.inr hf)

p2m_export "AlgebraicCurve.Place" "mem_compSubring_or_inv_mem"
private def _root_.AlgebraicCurve.Place.compValuationSubring (hw : Function.Surjective (algebraMap K w.ResidueField)) :
    ValuationSubring F :=
  ValuationSubring.ofSubring (w.compSubring A) (w.mem_compSubring_or_inv_mem A hw)

p2m_export "AlgebraicCurve.Place" "compValuationSubring"
@[scoped simp]
theorem compValuationSubring_toSubring (hw : Function.Surjective (algebraMap K
    w.ResidueField)) :
    (w.compValuationSubring A hw).toSubring = w.compSubring A := rfl

theorem mem_compValuationSubring_iff (hw : Function.Surjective (algebraMap K
    w.ResidueField))
    (f : F) : f ∈ w.compValuationSubring A hw ↔ f ∈ w.compSubring A := Iff.rfl

theorem mem_compSubring_of_isIntegral (hw : Function.Surjective (algebraMap K
    w.ResidueField))
    {S : Subring F} (hS : S ≤ w.compSubring A) {f : F} (hf : IsIntegral S f) :
    f ∈ w.compSubring A := by
  obtain ⟨p, hp, hpf⟩ := hf
  let V := w.compValuationSubring A hw
  let i : S →+* V := Subring.inclusion hS
  have hint : IsIntegral V f := by
    refine ⟨p.map i, hp.map i, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpf
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_isIntegral' [IsAlgClosed K] {S : Subring F} (hS : S ≤
    w.compSubring A)
    {f : F} (hf : IsIntegral S f) : f ∈ w.compSubring A := by
  obtain ⟨p, hp, hpf⟩ := hf
  have hSO : ∀ s : S, (s : F) ∈ w.toValuationSubring := fun s => w.compSubring_le A (hS s.2)
  have hfO : f ∈ w.toValuationSubring := by
    refine w.mem_of_eval_monic_eq_zero (P := p.map S.subtype) (hp.map _) (fun i => ?_) ?_
    · rw [Polynomial.coeff_map]
      exact hSO _
    · rw [Polynomial.eval_map]
      exact hpf
  let vS : S →+* A := (w.value A).comp (Subring.inclusion hS)
  let ιS : S →+* w.toValuationSubring := S.subtype.codRestrict _ hSO
  have hres : (residue w.toValuationSubring).comp ιS =
      ((algebraMap K w.ResidueField).comp (algebraMap A K)).comp vS := by
    ext s
    change residue w.toValuationSubring ⟨s, hSO s⟩ =
      algebraMap K w.ResidueField ((w.value A ⟨s, hS s.2⟩ : A) : K)
    exact (w.hasValueAt_iff_residue (hSO s) _).mp (w.hasValueAt_value A ⟨s, hS s.2⟩)
  set r : w.ResidueField := residue w.toValuationSubring ⟨f, hfO⟩ with hr
  let Q : Polynomial A := p.map vS
  have hQ : Q.Monic := hp.map _
  have hzero : Polynomial.eval₂ ιS ⟨f, hfO⟩ p = 0 := by
    apply Subtype.val_injective
    change w.toValuationSubring.subtype (Polynomial.eval₂ ιS ⟨f, hfO⟩ p) = ((0 :
        w.toValuationSubring) : F)
    rw [Polynomial.hom_eval₂]
    exact hpf
  have hrootκ : Polynomial.eval₂ (algebraMap K w.ResidueField) r (Q.map (algebraMap A K)) = 0 := by
    rw [Polynomial.eval₂_map, Polynomial.eval₂_map, ← hres, hr, ← Polynomial.hom_eval₂, hzero,
      map_zero]
  have hint : IsIntegral K r := ⟨Q.map (algebraMap A K), hQ.map _, hrootκ⟩
  obtain ⟨c, hc⟩ : r ∈ (algebraMap K w.ResidueField).range :=
    minpoly.mem_range_of_degree_eq_one K r
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))
  have hcroot : Polynomial.eval₂ (algebraMap A K) c Q = 0 := by
    apply (algebraMap K w.ResidueField).injective
    rw [Polynomial.hom_eval₂, ← Polynomial.eval₂_map, hc, hrootκ, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (⟨Q, hQ, hcroot⟩ : IsIntegral A c)
  refine ⟨y, (w.hasValueAt_iff_residue hfO _).mpr ?_⟩
  rw [← hr, ← hc, ← hy]
  rfl

p2m_export "AlgebraicCurve.Place" "mem_compSubring_of_isIntegral'"
end Place
p2m_reactivate "P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve.Place P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jq jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange"
p2m_open "ModularCurve"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve ModularCurve.CharPModel"

theorem exists_sub_mem_nonunits_of_integral_affineBaseInf'
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)))
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
    (hb : ∃ p : Polynomial (affineBaseInf M A), p.Monic ∧
      Polynomial.eval₂ (affineBaseInf M A).subtype b p = 0)
    (a₀ : A)
    (hj : 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full M (jq_mem M))⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))⁻¹
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
        (a₀ : AlgebraicClosure ℚ))) :
    ∃ a : A, (b - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
      (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits := by

  have hjinv : (jBar M)⁻¹ ∈ w.compSubring A :=
    w.mem_compSubring_of_hasValueAt (A := A) (a := (a₀ : AlgebraicClosure ℚ)) a₀.2
      (w.hasValueAt_of_ord_pos hj)
  have hS : affineBaseInf M A ≤ w.compSubring A := by
    rw [affineBaseInf, Subring.closure_le]
    rintro y (⟨c, rfl⟩ | rfl)
    · exact (w.algebraMap_mem_compSubring_iff (A := A) (c : AlgebraicClosure ℚ)).mpr c.2
    · exact hjinv
  have hint : IsIntegral (affineBaseInf M A) b := hb
  obtain ⟨a, ha⟩ := (w.mem_compSubring_iff (A := A)).mp
    (w.mem_compSubring_of_isIntegral' (A := A) hS hint)
  exact ⟨a, ha⟩

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve.Place P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve ModularCurve.CharPModel in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)))
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
    (hb : ∃ p : Polynomial (affineBaseInf M A), p.Monic ∧
      Polynomial.eval₂ (affineBaseInf M A).subtype b p = 0)
    (a₀ : A)
    (hj : 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full M (jq_mem M))⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))⁻¹
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
        (a₀ : AlgebraicClosure ℚ))) :
    ∃ a : A, (b - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
      (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits :=
  ModularCurve.exists_sub_mem_nonunits_of_integral_affineBaseInf' A M w b hb a₀ hj

end
p2m_reactivate "P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve.Place P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf.AlgebraicCurve"

end S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf
end P2MW
export P2MW.S_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf (solution)
