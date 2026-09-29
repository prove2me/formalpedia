-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_and_residueSnd_of_mem_nodePairsOfPlaces_of_nodePack
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c40645a8-7d07-580b-a6db-28509ef1c133

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_and_residueSnd_of_mem_nodePairsOfPlaces_of_nodePack
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace JacJ9NodeClause

section Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem hasValue_add (v : Place K F) {g g' : F} {a a' : K}
    (h : v.HasValue g a) (h' : v.HasValue g' a') : v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  rw [show (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ from rfl,
    map_add, hr, hr', map_add]

private theorem hasValue_zero_of_ord_pos (v : Place K F) {d : F} (hd : 0 < v.ord d) :
    v.HasValue d 0 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hd
    exact lt_irrefl _ hd
  have hmem : d ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hd0 hd.le
  refine ⟨hmem, ?_⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h0 := Place.ord_coe_unit (v := v) hu.unit
  rw [IsUnit.unit_spec] at h0
  change v.ord d = 0 at h0
  omega

private theorem hasValue_mul_zero (v : Place K F) {b y : F} (hb : b = 0 ∨ 0 ≤ v.ord b)
    (hy : v.ord y = 1) : v.HasValue (b * y) 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hy
    exact zero_ne_one hy
  by_cases hb0 : b = 0
  · rw [hb0, zero_mul, ← map_zero (algebraMap K F)]
    exact Place.hasValue_algebraMap v 0
  · apply hasValue_zero_of_ord_pos
    rw [Place.ord_mul v hb0 hy0, hy]
    have hb' : 0 ≤ v.ord b := hb.resolve_left hb0
    omega

end Values

section Exhaust

p2m_open "ModularCurve.NodeLocalized"

variable (M : ℕ) [NeZero M]

private theorem fieldOver_mono {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    fieldOver M K ≤ fieldOver M K' :=
  Subfield.closure_mono (Set.union_subset_union_left _ (by
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨c, h c.2⟩, rfl⟩))

private theorem exists_fieldOver_mem (f : ↥(modularFunctionFieldBar M)) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧
      ((f : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver M K := by
  have h : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M) := f.2
  rw [laurentBaseChange_adjoin_pair (AlgebraicClosure ℚ) M (functionFieldGeneration M)] at h
  have h' : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
        ∪ {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) M}) := h
  have h0 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(0 : AlgebraicClosure ℚ)}) :=
    IntermediateField.adjoin.finiteDimensional isIntegral_zero
  refine Subfield.closure_induction (p := fun x _ => ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ K ∧ x ∈ fieldOver M K) ?_ ?_ ?_ ?_ ?_ ?_ h'
  · rintro x (⟨c, rfl⟩ | hx)
    · refine ⟨IntermediateField.adjoin ℚ {c}, IntermediateField.adjoin.finiteDimensional
        (isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic c)), ?_⟩
      exact Subfield.subset_closure (Or.inl ⟨⟨c, IntermediateField.mem_adjoin_simple_self ℚ c⟩, rfl⟩)
    · exact ⟨IntermediateField.adjoin ℚ {(0 : AlgebraicClosure ℚ)}, h0, Subfield.subset_closure (Or.inr hx)⟩
  · exact ⟨IntermediateField.adjoin ℚ {(0 : AlgebraicClosure ℚ)}, h0, one_mem _⟩
  · rintro x y _ _ ⟨K₁, hK₁, hx⟩ ⟨K₂, hK₂, hy⟩
    haveI := hK₁
    haveI := hK₂
    exact ⟨K₁ ⊔ K₂, inferInstance,
      add_mem (fieldOver_mono M le_sup_left hx) (fieldOver_mono M le_sup_right hy)⟩
  · rintro x _ ⟨K₁, hK₁, hx⟩
    exact ⟨K₁, hK₁, neg_mem hx⟩
  · rintro x _ ⟨K₁, hK₁, hx⟩
    exact ⟨K₁, hK₁, inv_mem hx⟩
  · rintro x y _ _ ⟨K₁, hK₁, hx⟩ ⟨K₂, hK₂, hy⟩
    haveI := hK₁
    haveI := hK₂
    exact ⟨K₁ ⊔ K₂, inferInstance,
      mul_mem (fieldOver_mono M le_sup_left hx) (fieldOver_mono M le_sup_right hy)⟩

end Exhaust

section NodeRing

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private noncomputable def resOver₁ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N)) :
    ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

private noncomputable def resOver₂ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N)) :
    ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))

private theorem resOver₁_apply (g : ↥(R.nodeIntegersOver K w)) :
    resOver₁ R K w g = R.nodeResidue₁ w ⟨g, g.2.1⟩ := rfl

private theorem resOver₂_apply (g : ↥(R.nodeIntegersOver K w)) :
    resOver₂ R K w g = R.nodeResidue₂ w ⟨g, g.2.1⟩ := rfl

private theorem resOver₁_nodeConst (c : ↥(NodeLocalized.coeffSubring A K)) :
    resOver₁ R K w (R.nodeConst K w c) =
      algebraMap k ↥(modularFunctionFieldC k N) (red ⟨(c : AlgebraicClosure ℚ), c.2.1⟩) := by
  rw [resOver₁_apply, nodeResidue₁_apply,
    show (⟨((R.nodeConst K w c : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
        (R.nodeConst K w c).2.1.1⟩ : ↥R.R₁.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
          ((⟨(c : AlgebraicClosure ℚ), c.2.1⟩ : A) : AlgebraicClosure ℚ),
        (R.R₁.algebraMap_mem_iff _).mpr (⟨(c : AlgebraicClosure ℚ), c.2.1⟩ : A).2⟩ from rfl,
    residue₁_apply, R.R₁.residue_algebraMap]
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))
      (IsLocalRing.residue A ⟨(c : AlgebraicClosure ℚ), c.2.1⟩))
    = algebraMap k (LaurentSeries k) (red ⟨(c : AlgebraicClosure ℚ), c.2.1⟩)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single,
    R.redBar_residue]

private theorem resOver₂_nodeConst (c : ↥(NodeLocalized.coeffSubring A K)) :
    resOver₂ R K w (R.nodeConst K w c) =
      algebraMap k ↥(modularFunctionFieldC k N) (red ⟨(c : AlgebraicClosure ℚ), c.2.1⟩) := by
  rw [resOver₂_apply, nodeResidue₂_apply,
    show (⟨((R.nodeConst K w c : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
        (R.nodeConst K w c).2.1.2.1⟩ : ↥R.R₂.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
          ((⟨(c : AlgebraicClosure ℚ), c.2.1⟩ : A) : AlgebraicClosure ℚ),
        (R.R₂.algebraMap_mem_iff _).mpr (⟨(c : AlgebraicClosure ℚ), c.2.1⟩ : A).2⟩ from rfl,
    residue₂_apply, R.R₂.residue_algebraMap]
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))
      (IsLocalRing.residue A ⟨(c : AlgebraicClosure ℚ), c.2.1⟩))
    = algebraMap k (LaurentSeries k) (red ⟨(c : AlgebraicClosure ℚ), c.2.1⟩)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single,
    R.redBar_residue]

variable {K w}

private theorem hasValue_pair_of_pack [PerfectField k] (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hloc : IsLocalRing ↥(R.nodeIntegersOver K w))
    (hϖ0 : red ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0)
    (hmaxI : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K),
      ¬ IsUnit (g - R.nodeConst K w o))
    (hregB : ∀ g : ↥(R.nodeIntegersOver K w),
      (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
      (R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)))
    (g : ↥(R.nodeIntegersOver K w)) :
    ∃ c₀ : k, w.HasValue (R.residue₁ ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.1⟩) c₀ ∧
      (arithFrobC q k N • w).HasValue (R.residue₂ ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.2.1⟩) c₀ := by
  haveI := hloc
  obtain ⟨o, hunit⟩ := hres g
  have hm : g - R.nodeConst K w o ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hunit
  rw [hmaxI] at hm
  have hm₁ := Ideal.mem_span_insert.mp hm
  obtain ⟨a₁, z, hz, h1⟩ := hm₁
  have hm₂ := Ideal.mem_span_insert.mp hz
  obtain ⟨a₂, z', hz', h2⟩ := hm₂
  have hm₃ := Ideal.mem_span_singleton'.mp hz'
  obtain ⟨a₃, h3⟩ := hm₃
  have hg : g = R.nodeConst K w o + (a₁ * R.nodeConst K w ϖ + (a₂ * c.x + a₃ * c.y)) := by
    rw [← sub_eq_iff_eq_add', h1, h2, ← h3]
  have hϖ₁ : resOver₁ R K w (R.nodeConst K w ϖ) = 0 := by
    rw [resOver₁_nodeConst, hϖ0, map_zero]
  have hϖ₂ : resOver₂ R K w (R.nodeConst K w ϖ) = 0 := by
    rw [resOver₂_nodeConst, hϖ0, map_zero]
  have hx₁ : resOver₁ R K w c.x = 0 := c.x_fst
  have hy₁ : w.ord (resOver₁ R K w c.y) = 1 := c.y_fst
  have hy₂ : resOver₂ R K w c.y = 0 := c.y_snd
  have hx₂ : (arithFrobC q k N • w).ord (resOver₂ R K w c.x) = 1 := c.x_snd
  have hb₃ : resOver₁ R K w a₃ = 0 ∨ 0 ≤ w.ord (resOver₁ R K w a₃) := (hregB a₃).1
  have hb₂ : resOver₂ R K w a₂ = 0 ∨ 0 ≤ (arithFrobC q k N • w).ord (resOver₂ R K w a₂) := (hregB a₂).2
  have e₁ : resOver₁ R K w g = resOver₁ R K w (R.nodeConst K w o) + resOver₁ R K w a₃ * resOver₁ R K w c.y := by
    rw [hg]
    simp only [map_add, map_mul, hϖ₁, hx₁, mul_zero, zero_add]
  have e₂ : resOver₂ R K w g = resOver₂ R K w (R.nodeConst K w o) + resOver₂ R K w a₂ * resOver₂ R K w c.x := by
    rw [hg]
    simp only [map_add, map_mul, hϖ₂, hy₂, mul_zero, zero_add, add_zero]
  refine ⟨red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩, ?_, ?_⟩
  · have ho : w.HasValue (resOver₁ R K w (R.nodeConst K w o)) (red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩) := by
      rw [resOver₁_nodeConst]
      exact Place.hasValue_algebraMap w _
    have hv := hasValue_add w ho (hasValue_mul_zero w hb₃ hy₁)
    rw [add_zero, ← e₁, resOver₁_apply, nodeResidue₁_apply] at hv
    exact hv
  · have ho : (arithFrobC q k N • w).HasValue (resOver₂ R K w (R.nodeConst K w o))
        (red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩) := by
      rw [resOver₂_nodeConst]
      exact Place.hasValue_algebraMap (arithFrobC q k N • w) _
    have hv := hasValue_add (arithFrobC q k N • w) ho (hasValue_mul_zero (arithFrobC q k N • w) hb₂ hx₂)
    rw [add_zero, ← e₂, resOver₂_apply, nodeResidue₂_apply] at hv
    exact hv

end NodeRing

end JacJ9NodeClause

open JacJ9NodeClause in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) [PerfectField k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hmax : ∀ w ∈ W,
      ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
        ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
          ∃ (c : R.NodeCoordinates K' w) (ϖ : ↥(NodeLocalized.coeffSubring A K'))
            (_ : IsLocalRing ↥(R.nodeIntegersOver K' w)) (_ : IsNoetherianRing ↥(R.nodeIntegersOver K' w)),
            (∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d') ∧
            IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, c.x, c.y} ∧
            (∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o)) ∧
            ∀ g : ↥(R.nodeIntegersOver K' w),
              (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
              (R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩))) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
        ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.reduceFst V = s.1 → 0 ≤ V.ord f) →
        ∃ c : k, s.1.HasValue (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) c ∧
                 s.2.HasValue (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N) c := by
  intro f h₁ h₂ s hs hreg
  obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff _ _ s).mp hs
  have hfn : f ∈ R.nodeIntegers w := by
    refine ⟨h₁, h₂, fun V hV => ?_⟩
    by_cases hf0 : f = 0
    · rw [hf0]
      exact zero_mem _
    · exact Place.mem_of_ord_nonneg V hf0 (hreg V hV)
  obtain ⟨K₀, hK₀, hfK₀⟩ := JacJ9NodeClause.exists_fieldOver_mem (N * q) f
  obtain ⟨K', _, hKK', c, ϖ, hloc, _, hϖ, hmaxI, hres, hregB⟩ := hmax w hw K₀ hK₀
  have hϖ0 : red ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  exact JacJ9NodeClause.hasValue_pair_of_pack R c ϖ hloc hϖ0 hmaxI hres hregB
    ⟨f, hfn, JacJ9NodeClause.fieldOver_mono (N * q) hKK' hfK₀⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_and_residueSnd_of_mem_nodePairsOfPlaces_of_nodePack
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_and_residueSnd_of_mem_nodePairsOfPlaces_of_nodePack (solution)
