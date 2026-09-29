-- Prove2me | solution 1 for IntermediateField.finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c4354fdf-3735-5439-b16b-44a59c592dbc

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_trdeg_eq_one
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_of_linearDisjoint_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver

set_option autoImplicit false

open AlgebraicCurve

namespace FormDescent

section Constants

variable {L : Type} [Field L] (K₀ : Subfield L)
  {F : Type} [Field F] [Algebra L F]
  (hLalg : ∀ x : F, IsAlgebraic L x → x ∈ Set.range (algebraMap L F))
  (F₀ : Subfield F)
  (hconst : ∀ c : L, algebraMap L F c ∈ F₀ ↔ c ∈ K₀)
  [Algebra ↥K₀ ↥F₀]
  (hKF : ∀ c : ↥K₀, ((algebraMap ↥K₀ ↥F₀ c : ↥F₀) : F) = algebraMap L F (c : L))

omit hLalg F₀ hconst in
theorem algebraMap_KF_apply (c : ↥K₀) : algebraMap ↥K₀ F c = algebraMap L F (c : L) := rfl

include hKF in
theorem isScalarTower_K₀_F₀_F : IsScalarTower ↥K₀ ↥F₀ F := by
  constructor
  intro x y z
  show (((x • y : ↥F₀)) : F) • z = (x : L) • ((y : F) • z)
  rw [Algebra.smul_def x y, Subfield.coe_mul, hKF, smul_eq_mul, smul_eq_mul, Algebra.smul_def, mul_assoc]

include hLalg hconst hKF in

theorem mem_range_of_isAlgebraic_coe (x : ↥F₀) (hx : IsAlgebraic L (x : F)) :
    x ∈ Set.range (algebraMap ↥K₀ ↥F₀) := by
  obtain ⟨c, hc⟩ := hLalg _ hx
  have hcK : c ∈ K₀ := (hconst c).mp (hc ▸ x.2)
  refine ⟨⟨c, hcK⟩, Subtype.ext ?_⟩
  rw [hKF]; exact hc

include hLalg hconst hKF in

theorem mem_range_of_isAlgebraic (x : ↥F₀) (hx : IsAlgebraic ↥K₀ x) :
    x ∈ Set.range (algebraMap ↥K₀ ↥F₀) := by
  haveI := isScalarTower_K₀_F₀_F K₀ F₀ hKF
  refine mem_range_of_isAlgebraic_coe K₀ hLalg F₀ hconst hKF x ?_
  have h1 : IsAlgebraic ↥K₀ ((x : ↥F₀) : F) := hx.algebraMap (A := F)
  exact h1.extendScalars (algebraMap ↥K₀ L).injective

include hLalg hconst hKF in

theorem transcendental_coe (t : ↥F₀) (ht : Transcendental ↥K₀ t) : Transcendental L (t : F) := by
  intro halg
  obtain ⟨c, hc⟩ := mem_range_of_isAlgebraic_coe K₀ hLalg F₀ hconst hKF t halg
  exact ht (hc ▸ isAlgebraic_algebraMap c)

end Constants

section Transcendence

variable {L : Type} [Field L] [CharZero L] (K₀ : Subfield L)
  {F : Type} [Field F] [Algebra L F]
  (hLalg : ∀ x : F, IsAlgebraic L x → x ∈ Set.range (algebraMap L F))
  (F₀ : Subfield F)
  (hconst : ∀ c : L, algebraMap L F c ∈ F₀ ↔ c ∈ K₀)
  (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → ↥F₀) (d : Fin n → L) (g' : Fin n → ↥F₀),
      (∑ i, d i • (g' i : F)) ≠ 0 ∧ f * (∑ i, d i • (g' i : F)) = ∑ i, c i • (g i : F))
  [Algebra ↥K₀ ↥F₀]
  (hKF : ∀ c : ↥K₀, ((algebraMap ↥K₀ ↥F₀ c : ↥F₀) : F) = algebraMap L F (c : L))

include hLalg hconst hspan hKF in

theorem exists_transcendental [IsCurveOver L F] [Algebra.EssFiniteType L F] :
    ∃ t : ↥F₀, Transcendental ↥K₀ t := by
  by_contra hne
  simp only [not_exists] at hne

  have hF₀ : ∀ g : ↥F₀, ∃ c : L, (g : F) = algebraMap L F c := by
    intro g
    have halg : IsAlgebraic ↥K₀ g := by
      have := hne g
      rwa [Transcendental, not_not] at this
    obtain ⟨c, hc⟩ := mem_range_of_isAlgebraic K₀ hLalg F₀ hconst hKF g halg
    exact ⟨(c : L), by rw [← hc, hKF]⟩
  choose γ hγ using hF₀

  have hFalg : Algebra.IsAlgebraic L F := by
    refine ⟨fun f => ?_⟩
    obtain ⟨n, c, g, d, g', hden, hf⟩ := hspan f
    have hnum : (∑ i, c i • (g i : F)) = algebraMap L F (∑ i, c i * γ (g i)) := by
      rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [hγ, map_mul, Algebra.smul_def]
    have hden' : (∑ i, d i • (g' i : F)) = algebraMap L F (∑ i, d i * γ (g' i)) := by
      rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [hγ, map_mul, Algebra.smul_def]
    rw [hnum, hden'] at hf
    rw [hden'] at hden
    have hf' : f = algebraMap L F ((∑ i, c i * γ (g i)) / (∑ i, d i * γ (g' i))) := by
      rw [map_div₀, eq_div_iff hden, hf]
    rw [hf']
    exact isAlgebraic_algebraMap _
  have h0 : Algebra.trdeg L F = 0 := trdeg_eq_zero
  have h1 := AlgebraicCurve.IsCurveOver.trdeg_eq_one L F
  rw [h0] at h1
  exact zero_ne_one h1

end Transcendence

section LD

variable {L : Type} [Field L] [CharZero L] (K₀ : Subfield L) (hLK₀ : ∀ x : L, IsAlgebraic ↥K₀ x)
  {F : Type} [Field F] [Algebra L F]
  (hLalg : ∀ x : F, IsAlgebraic L x → x ∈ Set.range (algebraMap L F))
  (F₀ : Subfield F)
  (hconst : ∀ c : L, algebraMap L F c ∈ F₀ ↔ c ∈ K₀)
  (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → ↥F₀) (d : Fin n → L) (g' : Fin n → ↥F₀),
      (∑ i, d i • (g' i : F)) ≠ 0 ∧ f * (∑ i, d i • (g' i : F)) = ∑ i, c i • (g i : F))
  [Algebra ↥K₀ ↥F₀]
  (hKF : ∀ c : ↥K₀, ((algebraMap ↥K₀ ↥F₀ c : ↥F₀) : F) = algebraMap L F (c : L))

include hLK₀ hLalg hconst hspan in
omit [Algebra ↥K₀ ↥F₀] in

theorem ld_raw : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥(F₀.toSubring)), LinearIndependent ↥(K₀.toSubring) c →
      ∑ i, c i • ((a i : ↥F₀.toSubring) : F) = 0 → ∀ i, a i = 0 := by
  refine (AlgebraicCurve.NodeAnnulusEngine.linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn
    (k := ↥K₀) (L := L) (F := F) (⊥ : IntermediateField ↥K₀ L) ?_
    (Subfield.toIntermediateField F₀ (fun c => (hconst (c : L)).mpr c.2)) ?_ ?_ ?_
    K₀.toSubring ?_ ?_ F₀.toSubring (fun a ha => ha) (fun x hx => ⟨x, 1, hx, one_mem _, one_ne_zero, mul_one x⟩)).1
  ·
    intro y
    exact (hLK₀ y).extendScalars (algebraMap ↥K₀ ↥(⊥ : IntermediateField ↥K₀ L)).injective
  · intro y hy
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hy
    show algebraMap L F (c : L) ∈ F₀
    exact (hconst _).mpr c.2
  · intro f
    obtain ⟨n, c, g, d, g', hden, hf⟩ := hspan f
    exact ⟨n, c, fun i => (g i : F), n, d, fun i => (g' i : F), fun i => (g i).2, fun i => (g' i).2, hden, hf⟩
  · rintro x hx ⟨p, hp0, -, hpx⟩
    have halg : IsAlgebraic L x := ⟨p, hp0, by rwa [Polynomial.aeval_map_algebraMap] at hpx⟩
    obtain ⟨y, hy⟩ := hLalg x halg
    have hyK : y ∈ K₀ := (hconst y).mp (hy ▸ hx)
    exact ⟨y, IntermediateField.mem_bot.mpr ⟨⟨y, hyK⟩, rfl⟩, hy.symm⟩
  · intro c hc
    exact IntermediateField.mem_bot.mpr ⟨⟨c, hc⟩, rfl⟩
  · intro y hy
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hy
    exact ⟨c, 1, c.2, one_mem _, one_ne_zero, mul_one _⟩

include hKF in
omit [CharZero L] in
theorem coe_smul_F₀ (c : ↥K₀) (y : ↥F₀) : ((c • y : ↥F₀) : F) = (c : L) • (y : F) := by
  rw [Algebra.smul_def, Subfield.coe_mul, hKF, Algebra.smul_def]

include hLK₀ hLalg hconst hspan hKF in

theorem linearIndependent_coe (n : ℕ) (b : Fin n → ↥F₀) (hb : LinearIndependent ↥K₀ b) :
    LinearIndependent L (fun i => ((b i : ↥F₀) : F)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro lam hsum

  let W : Submodule ↥K₀ L := Submodule.span ↥K₀ (Set.range lam)
  haveI : Module.Finite ↥K₀ ↥W := Module.Finite.span_of_finite ↥K₀ (Set.finite_range lam)
  let B := Module.finBasis ↥K₀ ↥W
  have hlamW : ∀ i, lam i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let μ : Fin n → Fin (Module.finrank ↥K₀ ↥W) → ↥K₀ := fun i j => B.repr ⟨lam i, hlamW i⟩ j
  let e : Fin (Module.finrank ↥K₀ ↥W) → L := fun j => (B j : L)
  have hlam : ∀ i, lam i = ∑ j, (μ i j : L) * e j := by
    intro i
    have h := congrArg (fun w : ↥W => (w : L)) (B.sum_repr ⟨lam i, hlamW i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    rfl
  have he : LinearIndependent ↥K₀ e := B.linearIndependent.map' W.subtype (Submodule.ker_subtype W)

  let a : Fin (Module.finrank ↥K₀ ↥W) → ↥F₀ := fun j => ∑ i, μ i j • b i
  have ha : ∀ j, (a j : F) = ∑ i, (μ i j : L) • (b i : F) := by
    intro j
    show ((∑ i, μ i j • b i : ↥F₀) : F) = _
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => coe_smul_F₀ K₀ F₀ hKF _ _
  have hswap : ∑ j, e j • (a j : F) = ∑ i, lam i • (b i : F) := by
    simp_rw [ha, Finset.smul_sum, smul_smul, hlam, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]

  have he' : LinearIndependent ↥(K₀.toSubring) e := by
    rw [Fintype.linearIndependent_iff] at he ⊢
    intro g hg j
    have h := he (fun j => ⟨(g j : L), (g j).2⟩) (by
      rw [← hg]
      exact Finset.sum_congr rfl fun j _ => rfl) j
    exact Subtype.ext (congrArg Subtype.val h)
  have hzero := ld_raw K₀ hLK₀ hLalg F₀ hconst hspan _ e (fun j => ⟨(a j : F), (a j).2⟩) he'
    (by rw [← hsum, ← hswap])

  have ha0 : ∀ j, a j = 0 := fun j => Subtype.ext (congrArg Subtype.val (hzero j))
  have hμ : ∀ i j, μ i j = 0 := by
    intro i j
    have := (Fintype.linearIndependent_iff.mp hb) (fun i => μ i j) (ha0 j) i
    exact this
  intro i
  rw [hlam i]
  simp [hμ]

end LD

end FormDescent

open IsLocalRing in
theorem solution
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {L : Type} [Field L] [CharZero L] (ι₀ : A₀ →+* L) (hι₀ : Function.Injective ι₀)
    (K₀ : Subfield L) (hK₀A : ∀ a : A₀, ι₀ a ∈ K₀)
    (hK₀ : ∀ x : L, x ∈ K₀ → ∃ a b : A₀, b ≠ 0 ∧ x * ι₀ b = ι₀ a)

    (hLK₀ : ∀ x : L, IsAlgebraic ↥K₀ x)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (hLalg : ∀ x : F, IsAlgebraic L x → x ∈ Set.range (algebraMap L F))
    (F₀ : Subfield F)
    (hconst : ∀ c : L, algebraMap L F c ∈ F₀ ↔ c ∈ K₀)
    (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → ↥F₀) (d : Fin n → L) (g' : Fin n → ↥F₀),
      (∑ i, d i • (g' i : F)) ≠ 0 ∧ f * (∑ i, d i • (g' i : F)) = ∑ i, c i • (g i : F))

    (j₀ : A₀ →+* ↥F₀) (hj₀ : ∀ a : A₀, ((j₀ a : ↥F₀) : F) = algebraMap L F (ι₀ a))
    :
    letI : Algebra A₀ ↥F₀ := j₀.toAlgebra
    letI : Algebra A₀ ↥K₀ := (ι₀.codRestrict K₀ hK₀A).toAlgebra
    letI : Algebra ↥K₀ ↥F₀ :=
      (((algebraMap L F).comp K₀.subtype).codRestrict F₀ (fun c => (hconst (c : L)).mpr c.2)).toAlgebra
    IsFractionRing A₀ ↥K₀ ∧ IsScalarTower A₀ ↥K₀ ↥F₀ ∧
    (∃ t : ↥F₀, Transcendental A₀ t) ∧
    (∀ t : ↥F₀, Transcendental A₀ t →
      FiniteDimensional ↥(IntermediateField.adjoin ↥K₀ ({t} : Set ↥F₀)) ↥F₀ ∧
      Algebra.IsSeparable ↥(IntermediateField.adjoin ↥K₀ ({t} : Set ↥F₀)) ↥F₀) ∧
    IsIntegrallyClosedIn A₀ ↥F₀ := by
  letI instAF : Algebra A₀ ↥F₀ := j₀.toAlgebra
  letI instAK : Algebra A₀ ↥K₀ := (ι₀.codRestrict K₀ hK₀A).toAlgebra
  letI instKF : Algebra ↥K₀ ↥F₀ :=
    (((algebraMap L F).comp K₀.subtype).codRestrict F₀ (fun c => (hconst (c : L)).mpr c.2)).toAlgebra
  have hKF : ∀ c : ↥K₀, ((algebraMap ↥K₀ ↥F₀ c : ↥F₀) : F) = algebraMap L F (c : L) := fun _ => rfl
  have hAK : ∀ a : A₀, ((algebraMap A₀ ↥K₀ a : ↥K₀) : L) = ι₀ a := fun _ => rfl
  have hAF : ∀ a : A₀, algebraMap A₀ ↥F₀ a = j₀ a := fun _ => rfl

  have htower : IsScalarTower A₀ ↥K₀ ↥F₀ := by
    refine IsScalarTower.of_algebraMap_eq fun a => Subtype.ext ?_
    rw [hKF, hAK, hAF, hj₀]
  haveI := htower
  haveI := FormDescent.isScalarTower_K₀_F₀_F K₀ F₀ hKF

  have hinj : Function.Injective (algebraMap A₀ ↥K₀) := by
    intro a b h
    apply hι₀
    rw [← hAK, ← hAK, h]
  haveI : FaithfulSMul A₀ ↥K₀ := (faithfulSMul_iff_algebraMap_injective A₀ ↥K₀).mpr hinj
  have hfrac : IsFractionRing A₀ ↥K₀ := by
    refine IsFractionRing.of_field (R := A₀) (K := ↥K₀) fun z => ?_
    obtain ⟨a, b, hb, hz⟩ := hK₀ (z : L) z.2
    refine ⟨a, b, ?_⟩
    have hb' : (algebraMap A₀ ↥K₀ b : ↥K₀) ≠ 0 := fun h => hb (hinj (h.trans (map_zero _).symm))
    rw [eq_div_iff hb']
    apply Subtype.ext
    rw [Subfield.coe_mul, hAK, hAK]
    exact hz
  haveI := hfrac

  have htransK : ∀ t : ↥F₀, Transcendental A₀ t ↔ Transcendental ↥K₀ t := fun t => by
    rw [Transcendental, Transcendental, IsFractionRing.isAlgebraic_iff A₀ ↥K₀ ↥F₀]
  obtain ⟨t₀, ht₀⟩ := FormDescent.exists_transcendental K₀ hLalg F₀ hconst hspan hKF
  refine ⟨hfrac, htower, ⟨t₀, (htransK t₀).mpr ht₀⟩, fun t ht => ?_, ?_⟩
  ·
    have htK : Transcendental ↥K₀ t := (htransK t).mp ht
    have htL : Transcendental L ((t : ↥F₀) : F) := FormDescent.transcendental_coe K₀ hLalg F₀ hconst hKF t htK
    haveI : FiniteDimensional ↥(IntermediateField.adjoin L ({algebraMap ↥F₀ F t} : Set F)) F :=
      IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType htL
    have hFD : FiniteDimensional ↥(IntermediateField.adjoin ↥K₀ ({t} : Set ↥F₀)) ↥F₀ :=
      IntermediateField.finiteDimensional_adjoin_of_linearDisjoint_of_transcendental
        (K₀ := ↥K₀) (L := L) (F₀ := ↥F₀) (F := F)
        (FormDescent.linearIndependent_coe K₀ hLK₀ hLalg F₀ hconst hspan hKF) t htK
    haveI := hFD
    haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ↥K₀ ({t} : Set ↥F₀)) ↥F₀ :=
      Algebra.IsAlgebraic.of_finite _ _
    exact ⟨hFD, inferInstance⟩
  ·
    rw [isIntegrallyClosedIn_iff]
    refine ⟨?_, fun {x} hx => ?_⟩
    · intro a b h
      apply hι₀
      apply (algebraMap L F).injective
      rw [← hj₀, ← hj₀, ← hAF, ← hAF, h]
    · have halgK : IsAlgebraic ↥K₀ x := (IsFractionRing.isAlgebraic_iff A₀ ↥K₀ ↥F₀).mp hx.isAlgebraic
      obtain ⟨c, hc⟩ := FormDescent.mem_range_of_isAlgebraic K₀ hLalg F₀ hconst hKF x halgK
      have hcint : IsIntegral A₀ c := by
        rw [← isIntegral_algebraMap_iff (B := ↥F₀) (algebraMap ↥K₀ ↥F₀).injective, hc]
        exact hx
      obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A₀) (K := ↥K₀)).mp hcint
      refine ⟨a, ?_⟩
      rw [IsScalarTower.algebraMap_apply A₀ ↥K₀ ↥F₀, ha, hc]

end S_IntermediateField_finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver
end P2MW
export P2MW.S_IntermediateField_finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver (solution)
