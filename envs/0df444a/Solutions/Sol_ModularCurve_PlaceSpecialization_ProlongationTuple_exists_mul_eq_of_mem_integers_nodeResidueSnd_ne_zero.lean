-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/be3a8bf5-dcca-53ab-b542-60bad826ace3

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable scoped instance (priority := high) AnnulusLocBranch.instAlgebraResidueFieldFullC
    {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ) :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N) :=
  SubalgebraClass.toAlgebra (modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)

namespace AnnulusLocBranch

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

noncomputable def res₂ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) :
    ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

theorem res₂_apply (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (b : ↥(R.nodeIntegersOver K w)) :
    res₂ R K w b = R.nodeResidue₂ w ⟨b, b.2.1⟩ := rfl

def toR₂ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) : ↥(R.nodeIntegersOver K w) →+* ↥R.R₂.integers where
  toFun v := ⟨v, v.2.1.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem res₂_eq (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) :
    res₂ R K w v = R.ι (R.R₂.residue (toR₂ R K w v)) := rfl

theorem coe_toR₂ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) :
    ((toR₂ R K w v : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) = v := rfl

theorem not_isUnit_toR₂_nodeConst (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    ¬ IsUnit (toR₂ R K w (R.nodeConst K w ϖ)) := by
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  have hfval : ((toR₂ R K w (R.nodeConst K w ϖ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hg' : ((toR₂ R K w (R.nodeConst K w ϖ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) *
      (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    rw [← MulMemClass.coe_mul, hg]; rfl
  have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [hfval, h0, map_zero, zero_mul] at hg'
    exact zero_ne_one hg'
  have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
    rw [map_inv₀, ← hfval]
    exact (eq_inv_of_mul_eq_one_right hg')
  have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have := g.2
    rw [hginv] at this
    exact (R.R₂.algebraMap_mem_iff _).mp this
  exact hanu (isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩)

theorem res₂_nodeConst_eq_zero (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    res₂ R K w (R.nodeConst K w ϖ) = 0 := by
  rw [res₂_apply, nodeResidue₂_apply, residue₂_apply]
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  set f : ↥R.R₂.integers := ⟨((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
      (R.nodeConst K w ϖ).2.1.2.1⟩ with hf
  have hfval : (f : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  have hfnu : ¬ IsUnit f := by
    intro hu
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : (f : ↥(modularFunctionFieldBar (N * q))) * (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
      rw [← MulMemClass.coe_mul, hg]; rfl
    have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      rw [hfval, h0, map_zero, zero_mul] at hg'
      exact zero_ne_one hg'
    have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
        algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
      rw [map_inv₀, ← hfval]
      exact (eq_inv_of_mul_eq_one_right hg')
    have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      have := g.2
      rw [hginv] at this
      exact (R.R₂.algebraMap_mem_iff _).mp this
    apply hanu
    exact isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  have hmem : f ∈ maximalIdeal ↥R.R₂.integers := (mem_maximalIdeal _).mpr hfnu
  rw [← R.R₂.ker_residue, RingHom.mem_ker] at hmem
  show R.ι (R.R₂.residue f) = 0
  rw [hmem, map_zero]

theorem valuation_nodeConst_lt_one (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    R.R₂.integers.valuation ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) < 1 := by
  have hmem : toR₂ R K w (R.nodeConst K w ϖ) ∈ maximalIdeal ↥R.R₂.integers :=
    (mem_maximalIdeal _).mpr (not_isUnit_toR₂_nodeConst R K w ϖ hϖ)
  exact (ValuationSubring.valuation_lt_one_iff _ _).mp hmem

theorem valuation_eq_one_of_res₂_ne_zero (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) (h : res₂ R K w v ≠ 0) :
    R.R₂.integers.valuation (v : ↥(modularFunctionFieldBar (N * q))) = 1 := by
  have h1 : IsUnit (toR₂ R K w v) := by
    apply R.R₂.isUnit_of_residue_ne_zero
    intro h0
    exact h (by rw [res₂_eq, h0, map_zero])
  exact (ValuationSubring.valuation_eq_one_iff _ _).mp h1

section BranchKer

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
  (ϖ : ↥(NodeLocalized.coeffSubring A K))

theorem span_le_ker (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    Ideal.span {R.nodeConst K w ϖ, c.y} ≤ RingHom.ker (res₂ R K w) := by
  rw [Ideal.span_le]
  rintro z (rfl | rfl)
  · exact res₂_nodeConst_eq_zero R K w ϖ hϖ
  · show res₂ R K w c.y = 0
    rw [res₂_apply]
    exact c.y_snd

theorem ker_res₂_eq [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.y, c.x}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.y, c.x})
    (hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime) (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y}) :
    RingHom.ker (res₂ R K w) = Ideal.span {R.nodeConst K w ϖ, c.y} := by
  classical
  set 𝔮 : Ideal ↥(R.nodeIntegersOver K w) := Ideal.span {R.nodeConst K w ϖ, c.y} with h𝔮
  haveI : 𝔮.IsPrime := hpr
  haveI hloc : IsLocalRing ↥(R.nodeIntegersOver K w) := IsLocalRing.of_unique_max_ideal ⟨_, hmax.1, hmax.2⟩
  have hmaxB : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.y, c.x} :=
    hmax.2 _ (maximalIdeal.isMaximal _)
  refine le_antisymm ?_ (span_le_ker R K w c ϖ hϖ)

  set Q := ↥(R.nodeIntegersOver K w) ⧸ 𝔮
  set mkq : ↥(R.nodeIntegersOver K w) →+* Q := Ideal.Quotient.mk 𝔮
  haveI : IsDomain Q := Ideal.Quotient.isDomain 𝔮
  haveI : Nontrivial Q := inferInstance
  haveI : IsLocalRing Q := IsLocalRing.of_surjective' mkq Ideal.Quotient.mk_surjective
  have hybar_ne : mkq c.x ≠ 0 := fun h => hy (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hmaxQ : maximalIdeal Q = Ideal.span {mkq c.x} := by

    have hcomap : (maximalIdeal Q).comap mkq = maximalIdeal ↥(R.nodeIntegersOver K w) := by
      have := Ideal.comap_isMaximal_of_surjective mkq Ideal.Quotient.mk_surjective (K := maximalIdeal Q)
      exact (hmax.2 _ this).trans hmaxB.symm
    have hmap : maximalIdeal Q = (maximalIdeal ↥(R.nodeIntegersOver K w)).map mkq := by
      rw [← hcomap, Ideal.map_comap_of_surjective mkq Ideal.Quotient.mk_surjective]
    rw [hmap, hmaxB, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · have : mkq (R.nodeConst K w ϖ) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
        rw [this]; exact zero_mem _
      · have : mkq c.y = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        rw [this]; exact zero_mem _
      · exact Ideal.subset_span rfl
    · exact Ideal.span_mono (Set.singleton_subset_iff.mpr
        ⟨c.x, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)), rfl⟩)
  have hnotfield : ¬ IsField Q := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq (R := Q)).mp hF
    rw [hmaxQ, Ideal.span_singleton_eq_bot] at this
    exact hybar_ne this
  have hP : (maximalIdeal Q).IsPrincipal := ⟨⟨mkq c.x, hmaxQ⟩⟩
  haveI : IsDiscreteValuationRing Q := ((IsDiscreteValuationRing.TFAE Q hnotfield).out 0 4).mpr hP
  have hirr : Irreducible (mkq c.x) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (mkq c.x) hybar_ne hmaxQ

  intro s hs
  by_contra hsnot
  have hI : (RingHom.ker (res₂ R K w)).map mkq ≠ ⊥ := by
    intro hbot
    apply hsnot
    have : mkq s ∈ (RingHom.ker (res₂ R K w)).map mkq := Ideal.mem_map_of_mem _ hs
    rw [hbot, Ideal.mem_bot] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hirr
  have hyn : mkq c.x ^ n ∈ (RingHom.ker (res₂ R K w)).map mkq := by rw [hn]; exact Ideal.subset_span rfl
  rw [← map_pow, Ideal.mem_map_iff_of_surjective mkq Ideal.Quotient.mk_surjective] at hyn
  obtain ⟨t, ht, hty⟩ := hyn

  have hdiff : c.x ^ n - t ∈ 𝔮 := by
    rw [← Ideal.Quotient.eq, hty]
  have hyn' : c.x ^ n ∈ RingHom.ker (res₂ R K w) := by
    have := add_mem (span_le_ker R K w c ϖ hϖ hdiff) ht
    rwa [sub_add_cancel] at this
  rw [RingHom.mem_ker, map_pow] at hyn'
  have hy0 : res₂ R K w c.x = 0 := (pow_eq_zero_iff'.mp hyn').1
  rw [res₂_apply] at hy0
  exact c.nodeResidue₂_x_ne_zero hy0

end BranchKer

section Loc

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
  (ϖ : ↥(NodeLocalized.coeffSubring A K))

theorem nodeConst_ne_zero
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y}) (hx : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    R.nodeConst K w ϖ ≠ 0 := by
  intro h0
  rw [h0, zero_pow (by omega), zero_mul] at hxy
  rcases mul_eq_zero.mp hxy with hx0 | hy0
  · exact hx (hx0 ▸ zero_mem _)
  · exact hy (hy0 ▸ zero_mem _)

theorem loc_injective [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime] :
    Function.Injective (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))) :=
  IsLocalization.injective _ (le_nonZeroDivisors_of_noZeroDivisors (fun h => hpr.ne_top
    ((Ideal.eq_top_iff_one _).mpr (by
      have : (0 : ↥(R.nodeIntegersOver K w)) ∈ (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl := h
      exact absurd (zero_mem _) this))))

theorem loc_x_mem_span [(Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) c.y ∈
      Ideal.span {algebraMap ↥(R.nodeIntegersOver K w)
        (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (R.nodeConst K w ϖ)} := by
  let alg := algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))
  have hyu : IsUnit (alg c.x) :=
    IsLocalization.map_units (M := (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl) _ ⟨c.x, hy⟩
  obtain ⟨yi, hyi⟩ := hyu.exists_right_inv
  have hprod : alg c.y * alg c.x = alg (R.nodeConst K w ϖ ^ E * u) :=
    (map_mul alg c.y c.x).symm.trans (congrArg alg hxy)
  have e1 : R.nodeConst K w ϖ ^ E * u = R.nodeConst K w ϖ * (R.nodeConst K w ϖ ^ (E - 1) * u) := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hE]
  have hchain : alg c.y = (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) * alg (R.nodeConst K w ϖ) :=
    calc alg c.y = alg c.y * 1 := (mul_one _).symm
      _ = alg c.y * (alg c.x * yi) := congrArg (alg c.y * ·) hyi.symm
      _ = (alg c.y * alg c.x) * yi := (mul_assoc _ _ _).symm
      _ = alg (R.nodeConst K w ϖ ^ E * u) * yi := congrArg (· * yi) hprod
      _ = alg (R.nodeConst K w ϖ * (R.nodeConst K w ϖ ^ (E - 1) * u)) * yi := congrArg (fun t => alg t * yi) e1
      _ = (alg (R.nodeConst K w ϖ) * alg (R.nodeConst K w ϖ ^ (E - 1) * u)) * yi :=
          congrArg (· * yi) (map_mul alg _ _)
      _ = alg (R.nodeConst K w ϖ) * (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) := mul_assoc _ _ _
      _ = (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) * alg (R.nodeConst K w ϖ) := mul_comm _ _
  exact Ideal.mem_span_singleton'.mpr ⟨_, hchain.symm⟩

theorem loc_maximalIdeal_eq [(Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    maximalIdeal (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) =
      Ideal.span {algebraMap ↥(R.nodeIntegersOver K w)
        (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (R.nodeConst K w ϖ)} := by
  have hxmem := loc_x_mem_span R K w c ϖ hy E hE u hxy
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · exact Ideal.subset_span rfl
    · exact hxmem
  · exact Ideal.span_mono (fun o ho => ⟨R.nodeConst K w ϖ, Set.mem_insert _ _, (Set.mem_singleton_iff.mp ho).symm⟩)

theorem loc_isDiscreteValuationRing [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y}) (hx : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) := by
  let O := Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})
  let alg := algebraMap ↥(R.nodeIntegersOver K w) O
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl O
    inferInstance
  haveI : IsDomain O := IsLocalization.isDomain_localization
    (le_nonZeroDivisors_of_noZeroDivisors (fun h => by
      have : (0 : ↥(R.nodeIntegersOver K w)) ∈ (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl := h
      exact absurd (zero_mem _) this))
  have hmaxO := loc_maximalIdeal_eq R K w c ϖ hy E hE u hxy
  have hϖO0 : alg (R.nodeConst K w ϖ) ≠ 0 := fun h =>
    nodeConst_ne_zero R K w c ϖ hy hx E hE u hxy ((loc_injective R K w c ϖ) (h.trans (map_zero alg).symm))
  have hϖOmem : alg (R.nodeConst K w ϖ) ∈ maximalIdeal O := by rw [hmaxO]; exact Ideal.subset_span rfl
  have hnotfield : ¬ IsField O := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq (R := O)).mp hF
    rw [this] at hϖOmem
    exact hϖO0 ((Ideal.mem_bot).mp hϖOmem)
  have hP : (maximalIdeal O).IsPrincipal := ⟨⟨alg (R.nodeConst K w ϖ), hmaxO⟩⟩
  exact ((IsDiscreteValuationRing.TFAE O hnotfield).out 0 4).mpr hP

theorem loc_irreducible [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y}) (hx : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    Irreducible (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (R.nodeConst K w ϖ)) := by
  haveI := loc_isDiscreteValuationRing R K w c ϖ hy hx E hE u hxy
  have hϖO0 : algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (R.nodeConst K w ϖ) ≠ 0 := fun h =>
    nodeConst_ne_zero R K w c ϖ hy hx E hE u hxy ((loc_injective R K w c ϖ) (h.trans (map_zero _).symm))
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hϖO0
    (loc_maximalIdeal_eq R K w c ϖ hy E hE u hxy)

theorem exists_surj_of_unit [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (wu : (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))ˣ) :
    ∃ p : ↥(R.nodeIntegersOver K w) × ↥(Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl,
      (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) *
          algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) p.2 =
        algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) p.1 ∧
      p.1 ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by
  obtain ⟨p, hp⟩ := IsLocalization.surj (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl
    (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))
  refine ⟨p, hp, fun ht => ?_⟩
  have htunit : IsUnit (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) p.1) := by
    rw [← hp]
    exact (Units.isUnit wu).mul (IsLocalization.map_units (M := (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl) _ p.2)
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (Ideal.span {R.nodeConst K w ϖ, c.y}) p.1).mpr ht
  exact (mem_maximalIdeal _).mp hmem htunit

theorem exists_mul_eq_of_eq_unit_mul_pow [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (b : ↥(R.nodeIntegersOver K w)) (m : ℕ)
    (wu : (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))ˣ)
    (hbw : algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) b =
      (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) *
        algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))
          (R.nodeConst K w ϖ) ^ m) :
    ∃ (s t : ↥(R.nodeIntegersOver K w)),
      s ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧ t ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧
      b * s = R.nodeConst K w ϖ ^ m * t := by
  let alg := algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))
  obtain ⟨p, hp, htmem⟩ := exists_surj_of_unit R K w c ϖ wu
  refine ⟨p.2, p.1, p.2.2, htmem, loc_injective R K w c ϖ ?_⟩
  have e2 : alg (R.nodeConst K w ϖ ^ m * p.1) = alg (R.nodeConst K w ϖ) ^ m * alg p.1 :=
    (map_mul alg _ _).trans (congrArg (· * alg p.1) (map_pow alg _ m))
  calc alg (b * p.2) = alg b * alg p.2 := map_mul alg b p.2
    _ = ((wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) * alg (R.nodeConst K w ϖ) ^ m) * alg p.2 :=
        congrArg (· * alg p.2) hbw
    _ = ((wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) * alg p.2) * alg (R.nodeConst K w ϖ) ^ m :=
        mul_right_comm _ _ _
    _ = alg p.1 * alg (R.nodeConst K w ϖ) ^ m := congrArg (· * alg (R.nodeConst K w ϖ) ^ m) hp
    _ = alg (R.nodeConst K w ϖ) ^ m * alg p.1 := mul_comm _ _
    _ = alg (R.nodeConst K w ϖ ^ m * p.1) := e2.symm

theorem exists_mul_eq_pow_mul [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime) (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hx : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u)
    (b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0) :
    ∃ (m : ℕ) (s t : ↥(R.nodeIntegersOver K w)),
      s ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧ t ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧
      b * s = R.nodeConst K w ϖ ^ m * t := by
  haveI := hpr
  haveI := loc_isDiscreteValuationRing R K w c ϖ hy hx E hE u hxy
  have hirr := loc_irreducible R K w c ϖ hy hx E hE u hxy
  have hbO : algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) b ≠ 0 := fun h =>
    hb ((loc_injective R K w c ϖ) (h.trans (map_zero _).symm))
  obtain ⟨m, wu, hbw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbO hirr
  obtain ⟨s, t, hs, ht, hst⟩ := exists_mul_eq_of_eq_unit_mul_pow R K w c ϖ b m wu hbw
  exact ⟨m, s, t, hs, ht, hst⟩

theorem cross_identity (a b sa ta sb tb ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (z : ↥(modularFunctionFieldBar (N * q)))
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a)
    (hfa : a * sa = ϖB ^ ma * ta) (hfb : b * sb = ϖB ^ mb * tb) :
    z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) := by
  have h1 : (b : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) := by
    have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfb
    simpa using this
  have h2 : (a : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) := by
    have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfa
    simpa using this
  calc z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * ↑tb * ↑sa = z * (↑b * ↑sb) * ↑sa := by rw [h1]; ring
    _ = (↑a * ↑sa) * ↑sb := by rw [← hzab]; ring
    _ = _ := by rw [h2]

theorem good_case (ta sb tb sa ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (hle : mb ≤ ma) (z : ↥(modularFunctionFieldBar (N * q)))
    (hϖ0 : (ϖB : ↥(modularFunctionFieldBar (N * q))) ≠ 0)
    (key : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) :
    z * ((tb * sa : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = ((ϖB ^ (ma - mb) * ta * sb : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) := by
  have hpow : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (ma - mb) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  have hmul : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (z * ((tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * ((ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (ma - mb) * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) := by
    linear_combination key + ((ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) * hpow
  have hfin := mul_left_cancel₀ (pow_ne_zero _ hϖ0) hmul
  push_cast
  exact hfin

theorem bad_case {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (val : Valuation ↥(modularFunctionFieldBar (N * q)) Γ)
    (ta sb tb sa ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (hlt : ma < mb) (z : ↥(modularFunctionFieldBar (N * q)))
    (hϖ0 : (ϖB : ↥(modularFunctionFieldBar (N * q))) ≠ 0) (hϖlt : val (ϖB : ↥(modularFunctionFieldBar (N * q))) < 1) (hz : val z ≤ 1)
    (hta : val (ta : ↥(modularFunctionFieldBar (N * q))) = 1) (hsb : val (sb : ↥(modularFunctionFieldBar (N * q))) = 1)
    (htb : val (tb : ↥(modularFunctionFieldBar (N * q))) = 1) (hsa : val (sa : ↥(modularFunctionFieldBar (N * q))) = 1)
    (key : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) : False := by
  have hpow : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le]
  have key2 : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) = (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) := by
    apply mul_left_cancel₀ (pow_ne_zero ma hϖ0)
    linear_combination key - (z * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q)))) * hpow
  have hv := congrArg val key2
  rw [map_mul, map_mul, map_mul, map_pow, map_mul, hta, hsb, htb, hsa, mul_one, mul_one, mul_one] at hv
  have hpk : val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) < 1 := pow_lt_one₀ zero_le' hϖlt (by omega)
  have hle1 : val z * val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) ≤
      val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) := by
    have := mul_le_mul_left hz (val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma))
    rwa [one_mul] at this
  rw [hv] at hle1
  exact absurd (lt_of_le_of_lt hle1 hpk) (lt_irrefl _)

theorem exists_mul_eq_of_mem_integers [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.y, c.x}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.y, c.x})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧
      c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧ c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u)
    (a b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0)
    (z : ↥(modularFunctionFieldBar (N * q))) (hz : z ∈ R.R₂.integers)
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a) :
    ∃ a' b' : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨b', b'.2.1⟩ ≠ 0 ∧ z * (b' : ↥(modularFunctionFieldBar (N * q))) = a' := by
  classical
  have hker := ker_res₂_eq R K w c ϖ hϖ hmax hbr.1 hbr.2.2.1
  have hres_of_notmem : ∀ v : ↥(R.nodeIntegersOver K w), v ∉ Ideal.span {R.nodeConst K w ϖ, c.y} → res₂ R K w v ≠ 0 := by
    intro v hv h0
    exact hv (by rw [← hker]; exact h0)
  by_cases ha : a = 0
  · refine ⟨0, 1, ?_, ?_⟩
    · have : res₂ R K w 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
      exact this
    · have hb' : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hb (Subtype.ext h)
      have hz0 : z = 0 := by
        have : z * (b : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hzab, ha]; rfl
        exact (mul_eq_zero.mp this).resolve_right hb'
      rw [hz0, zero_mul]; rfl
  obtain ⟨ma, sa, ta, hsa, hta, hfa⟩ :=
    exists_mul_eq_pow_mul R K w c ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 E hE u hu hxy a ha
  obtain ⟨mb, sb, tb, hsb, htb, hfb⟩ :=
    exists_mul_eq_pow_mul R K w c ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 E hE u hu hxy b hb
  have hϖB0 := nodeConst_ne_zero R K w c ϖ hbr.2.2.1 hbr.2.2.2 E hE u hxy
  have hϖF0 : ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => hϖB0 (Subtype.ext h0)
  have key := cross_identity R K w a b sa ta sb tb (R.nodeConst K w ϖ) ma mb z hzab hfa hfb
  rcases le_or_gt mb ma with hle | hlt
  · refine ⟨R.nodeConst K w ϖ ^ (ma - mb) * ta * sb, tb * sa, ?_,
      good_case R K w ta sb tb sa (R.nodeConst K w ϖ) ma mb hle z hϖF0 key⟩
    have : res₂ R K w (tb * sa) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero (hres_of_notmem tb htb) (hres_of_notmem sa hsa)
    exact this
  · exact (bad_case R K w R.R₂.integers.valuation ta sb tb sa (R.nodeConst K w ϖ) ma mb hlt z hϖF0
      (valuation_nodeConst_lt_one R K w ϖ hϖ)
      ((ValuationSubring.valuation_le_one_iff R.R₂.integers z).mpr hz)
      (valuation_eq_one_of_res₂_ne_zero R K w ta (hres_of_notmem ta hta))
      (valuation_eq_one_of_res₂_ne_zero R K w sb (hres_of_notmem sb hsb))
      (valuation_eq_one_of_res₂_ne_zero R K w tb (hres_of_notmem tb htb))
      (valuation_eq_one_of_res₂_ne_zero R K w sa (hres_of_notmem sa hsa)) key).elim

end Loc

end AnnulusLocBranch

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (a b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0)
    (z : ↥(modularFunctionFieldBar (N * q))) (hz : z ∈ R.R₂.integers)
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a) :
    ∃ a' b' : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨b', b'.2.1⟩ ≠ 0 ∧
      z * (b' : ↥(modularFunctionFieldBar (N * q))) = a' := by
  have hS : (Ideal.span {R.nodeConst K w ϖ, c.y, c.x} : Ideal ↥(R.nodeIntegersOver K w)) =
      Ideal.span {R.nodeConst K w ϖ, c.x, c.y} := by
    show Ideal.span (insert _ {c.y, c.x}) = Ideal.span (insert _ {c.x, c.y})
    rw [Set.pair_comm]
  have hmax' : (Ideal.span {R.nodeConst K w ϖ, c.y, c.x}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.y, c.x} := by
    rw [hS]; exact hmax
  exact AnnulusLocBranch.exists_mul_eq_of_mem_integers R K w c ϖ ((hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩)
    hmax' ⟨hbr.2.1, hbr.1, hbr.2.2.2, hbr.2.2.1⟩ E hE u hu ((mul_comm c.y c.x).trans hxy) a b hb z hz hzab

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero (solution)
