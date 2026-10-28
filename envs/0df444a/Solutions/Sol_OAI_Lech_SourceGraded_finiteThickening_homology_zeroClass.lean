-- Prove2me | solution 1 for OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:42:56.354286+00:00
-- url     : https://prove2.me/submissions/2fca8d87-eb11-4ef7-94d8-11335846eee6

import Mathlib
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L029

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section


universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]


variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma eq_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N) : ℓ.value M = ℓ.value N :=
  le_antisymm (ℓ.le_of_mono e.hom hN) (ℓ.le_of_mono e.inv hM)

end TorsionLength
end


universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

lemma powerTorsion_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (hM : powerTorsion I (ModuleCat.of R M)) (hN : powerTorsion I (ModuleCat.of R N)) :
    powerTorsion I (ModuleCat.of R (M × N)) := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨b, hb⟩ := hN
  refine ⟨max a b, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext
  · exact Module.mem_annihilator.mp (ha (Ideal.pow_le_pow_right (le_max_left a b) hr)) x.1
  · exact Module.mem_annihilator.mp (hb (Ideal.pow_le_pow_right (le_max_right a b) hr)) x.2

lemma powerTorsion_fin {M : Type u} [AddCommGroup M] [Module R M] (n : ℕ)
    (hM : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (Fin n → M)) := by
  obtain ⟨a, ha⟩ := hM
  refine ⟨a, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext i
  exact Module.mem_annihilator.mp (ha hr) (x i)

namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma additive_linear {M N P : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (he : Function.Exact f g)
    (ht : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R N) =
      ℓ.value (ModuleCat.of R M) + ℓ.value (ModuleCat.of R P) := by
  let S := ShortComplex.moduleCatMk f g (LinearMap.range_le_ker_iff.mp
    ((LinearMap.exact_iff.mp he).symm.le))
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr he
      mono_f := (ModuleCat.mono_iff_injective _).mpr hf
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }
  exact ℓ.additive hS ht

lemma value_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (hM : powerTorsion I (ModuleCat.of R M)) (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R (M × N)) =
      ℓ.value (ModuleCat.of R M) + ℓ.value (ModuleCat.of R N) := by
  apply ℓ.additive_linear (LinearMap.inl R M N) (LinearMap.snd R M N)
  · intro x y h
    exact congrArg Prod.fst h
  · intro n
    exact ⟨(0, n), rfl⟩
  · intro ⟨m, n⟩
    simp only [LinearMap.snd_apply]
    constructor
    · intro hn
      exact ⟨m, by simp [hn]⟩
    · rintro ⟨x, hx⟩
      exact (congrArg Prod.snd hx).symm
  · exact powerTorsion_prod hM hN

lemma value_linearEquiv {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R M) = ℓ.value (ModuleCat.of R N) := by
  let e' := e.toModuleIso
  exact ℓ.eq_of_iso e' ((powerTorsion I).prop_of_iso e'.symm hN) hN

lemma value_fin {M : Type u} [AddCommGroup M] [Module R M]
    (hM : powerTorsion I (ModuleCat.of R M)) (n : ℕ) :
    ℓ.value (ModuleCat.of R (Fin n → M)) = n • ℓ.value (ModuleCat.of R M) := by
  induction n with
  | zero =>
    rw [ℓ.zero (ModuleCat.isZero_iff_subsingleton.mpr inferInstance), zero_nsmul]
  | succ n ih =>
    let e : (Fin (n + 1) → M) ≃ₗ[R] M × (Fin n → M) :=
      (LinearEquiv.piCongrLeft R (fun _ : Option (Fin n) => M) (finSuccEquiv n)) ≪≫ₗ
        LinearEquiv.piOptionEquivProd R
    rw [ℓ.value_linearEquiv e (powerTorsion_prod hM (powerTorsion_fin _ hM)),
      ℓ.value_prod hM (powerTorsion_fin _ hM), ih, succ_nsmul, add_comm]

end TorsionLength
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLevel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech
universe u
variable {R : Type u} [CommRing R]
namespace IdealFiltration

lemma inclusion_injective (I J : Ideal R) (n : ℕ) :
    Function.Injective (inclusion I J n) := by
  rw [← LinearMap.ker_eq_bot, inclusion, Submodule.ker_liftQ_eq_bot]
  simpa only [LinearMap.ker_comp, Submodule.ker_mkQ, next] using (le_refl (next I J n))

lemma transition_surjective (I J : Ideal R) (n : ℕ) :
    Function.Surjective (transition I J n) := by
  intro x
  obtain ⟨a, rfl⟩ := (level I J n).mkQ_surjective x
  exact ⟨(level I J (n + 1)).mkQ a, rfl⟩

lemma piece_exact (I J : Ideal R) (n : ℕ) :
    Function.Exact (inclusion I J n) (transition I J n) := by
  rw [LinearMap.exact_iff]
  simp only [inclusion, transition, Submodule.ker_mapQ, Submodule.range_liftQ,
    LinearMap.range_comp, Submodule.range_subtype, Submodule.comap_id]

lemma quotient_torsion (I J : Ideal R) (n : ℕ) :
    powerTorsion I (ModuleCat.of R (R ⧸ level I J n)) := by
  refine ⟨n, ?_⟩
  rw [Ideal.annihilator_quotient]
  exact le_sup_left

lemma length_successor (I J : Ideal R) (ℓ : TorsionLength I) (n : ℕ) :
    ℓ.value (ModuleCat.of R (R ⧸ level I J (n + 1))) =
      ℓ.value (ModuleCat.of R (Piece I J n)) +
      ℓ.value (ModuleCat.of R (R ⧸ level I J n)) :=
  ℓ.additive_linear (inclusion I J n) (transition I J n)
    (inclusion_injective I J n) (transition_surjective I J n) (piece_exact I J n)
    (quotient_torsion I J _)

lemma length_eq_sum (I J : Ideal R) (ℓ : TorsionLength I) (N : ℕ) :
    ℓ.value (ModuleCat.of R (R ⧸ level I J N)) =
      ∑ n ∈ Finset.range N, ℓ.value (ModuleCat.of R (Piece I J n)) := by
  induction N with
  | zero =>
    have hz : CategoryTheory.Limits.IsZero (ModuleCat.of R (R ⧸ level I J 0)) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      simp only [level, pow_zero, Ideal.one_eq_top, top_sup_eq]
      infer_instance
    simp [ℓ.zero hz]
  | succ N ih => rw [length_successor, ih, Finset.sum_range_succ, add_comm]

lemma length_quotient (I J : Ideal R) (ℓ : TorsionLength I)
    (N : ℕ) (hN : I ^ N ≤ J) :
    ℓ.value (ModuleCat.of R (R ⧸ J)) =
      ∑ n ∈ Finset.range N, ℓ.value (ModuleCat.of R (Piece I J n)) := by
  have h : level I J N = J := sup_eq_right.mpr hN
  exact (congrArg (fun K : Ideal R => ℓ.value (ModuleCat.of R (R ⧸ K))) h).symm.trans
    (length_eq_sum I J ℓ N)

end IdealFiltration
end Lech

open CategoryTheory
namespace Lech
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

lemma powerTorsion_quotient : powerTorsion I (ModuleCat.of R (R ⧸ I)) := by
  refine ⟨1, ?_⟩
  rw [pow_one, Ideal.annihilator_quotient]

lemma powerTorsion_pi_small {M : Type u} [AddCommGroup M] [Module R M] (ι : Type)
    (hM : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (ι → M)) := by
  obtain ⟨a, ha⟩ := hM
  refine ⟨a, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext i
  exact Module.mem_annihilator.mp (ha hr) (x i)

namespace TorsionLength
variable (ℓ : TorsionLength I)
lemma value_fintype_small {M : Type u} [AddCommGroup M] [Module R M]
    (hM : powerTorsion I (ModuleCat.of R M)) (ι : Type) [Fintype ι] :
    ℓ.value (ModuleCat.of R (ι → M)) = Fintype.card ι • ℓ.value (ModuleCat.of R M) := by
  classical
  let e : (ι → M) ≃ₗ[R] (Fin (Fintype.card ι) → M) :=
    LinearEquiv.piCongrLeft R (fun _ => M) (Fintype.equivFin ι)
  exact (ℓ.value_linearEquiv e (powerTorsion_fin _ hM)).trans (ℓ.value_fin hM _)
end TorsionLength

namespace ResidueGenerators
variable {M : Type u} [AddCommGroup M] [Module R M]
    (hM : I ≤ Module.annihilator R M)

variable {ι : Type} [Fintype ι]

lemma generators_mem_range (v : ι → M) (i : ι) : v i ∈ (map hM v).range := by
  classical
  refine ⟨(Finsupp.linearEquivFunOnFinite R (R ⧸ I) ι) (Finsupp.single i 1), ?_⟩
  simp only [map, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Finsupp.lsum_single]
  change (coefficient hM (v i)) (Ideal.Quotient.mk I 1) = v i
  rw [coefficient_mk, one_smul]

lemma surjective_of_span (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Function.Surjective (map hM v) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hv, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact generators_mem_range hM v i

include hM in
lemma value_le (ℓ : TorsionLength I) (v : ι → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    ℓ.value (ModuleCat.of R M) ≤ Fintype.card ι • ℓ.value (ModuleCat.of R (R ⧸ I)) := by
  have : Epi (ModuleCat.ofHom (map hM v)) :=
    (ModuleCat.epi_iff_surjective _).mpr (surjective_of_span hM v hv)
  exact (ℓ.le_of_epi (ModuleCat.ofHom (map hM v))
    (powerTorsion_pi_small _ powerTorsion_quotient)).trans_eq
      (ℓ.value_fintype_small powerTorsion_quotient _)

end ResidueGenerators
end Lech


namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma span_subquotient {ι : Type*} (P Q : Submodule R R) (hQP : Q ≤ P)
    (v : ι → P) (hv : P ≤ Submodule.span R (Set.range (fun i => (v i : R))) ⊔ Q) :
    Submodule.span R (Set.range (fun i =>
      (Submodule.comap P.subtype Q).mkQ (v i))) = ⊤ := by
  change Submodule.span R (Set.range ((Submodule.comap P.subtype Q).mkQ ∘ v)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, Submodule.map_mkQ_eq_top]
  apply Submodule.map_injective_of_injective P.injective_subtype
  rw [Submodule.map_sup, Submodule.map_comap_subtype, inf_eq_right.mpr hQP,
    Submodule.map_span, Submodule.map_subtype_top]
  change Q ⊔ Submodule.span R (P.subtype '' Set.range v) = P
  rw [← Set.range_comp]
  apply le_antisymm
  · exact sup_le hQP (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => (v i).property))
  · simpa only [sup_comm, Function.comp_def, Submodule.subtype_apply] using hv

namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)

lemma monic_mem_powers {a : ℕ} {d : Fin h →₀ ℕ} (i : Fin h) (hd : a ≤ d i) :
    monic z d ∈ Ideal.span (Set.range (fun i => z i ^ a)) := by
  have hs : Finsupp.single i a ≤ d := Finsupp.single_le_iff.mpr hd
  obtain ⟨e, rfl⟩ := exists_add_of_le hs
  simp only [monic, MvPolynomial.monomial_single_add, map_mul, map_pow,
    MvPolynomial.eval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)


lemma exists_bounded {a n : ℕ} (d : Fin h →₀ ℕ) (hn : d.degree = n)
    (hd : ∀ i, d i < a) : ∃ e : Bounded h a n, exponent e = d := by
  refine ⟨⟨fun i => ⟨d i, hd i⟩, ?_⟩, ?_⟩
  · exact (Finsupp.degree_eq_sum d).symm.trans hn
  · ext i
    simp [exponent]

lemma power_le_bounded_span (a n : ℕ) :
    Ideal.span (Set.range z) ^ n ≤
      Ideal.span (Set.range (fun e : Bounded h a n => monic z (exponent e))) ⊔
      Ideal.span (Set.range (fun i => z i ^ a)) := by
  classical
  rw [span_monic_degree, Ideal.span_le]
  rintro _ ⟨d, hd, rfl⟩
  by_cases hd' : ∀ i, d i < a
  · obtain ⟨e, rfl⟩ := exists_bounded d hd hd'
    exact (show Ideal.span (Set.range (fun e : Bounded h a n => monic z (exponent e))) ≤ _ from le_sup_left) (Ideal.subset_span ⟨e, rfl⟩)
  · obtain ⟨i, hi⟩ := not_forall.mp hd'
    exact (show Ideal.span (Set.range (fun i => z i ^ a)) ≤ _ from le_sup_right) (monic_mem_powers z i (Nat.le_of_not_gt hi))

end MonomialSpanning



namespace IdealFiltration
lemma piece_annihilator (I J : Ideal R) (n : ℕ) :
    I ≤ Module.annihilator R (Piece I J n) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨x, rfl⟩ := (next I J n).mkQ_surjective x
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change r * (x : R) ∈ I ^ (n + 1) ⊔ J
  have hm : I * level I J n ≤ level I J (n + 1) := by
    simp only [level, Ideal.mul_sup, pow_succ']
    exact sup_le_sup_left Ideal.mul_le_right _
  exact hm (Ideal.mul_mem_mul hr x.property)
end IdealFiltration

namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)

lemma pieceGenerator_span (a n : ℕ) :
    Submodule.span R (Set.range (pieceGenerator z a n)) = ⊤ := by
  apply span_subquotient _ _ (IdealFiltration.level_succ_le _ _ _) (lift z a n)
  apply sup_le
  · exact (power_le_bounded_span z a n).trans
      (sup_le_sup_left (show Ideal.span (Set.range (fun i => z i ^ a)) ≤
        IdealFiltration.level _ _ (n+1) from le_sup_right) _)
  · exact le_sup_of_le_right le_sup_right

lemma piece_value_le (ℓ : TorsionLength (Ideal.span (Set.range z))) (a n : ℕ) :
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n)) ≤
      Fintype.card (Bounded h a n) •
        ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  let I : Ideal R := Ideal.span (Set.range z)
  let J : Ideal R := Ideal.span (Set.range (fun i => z i ^ a))
  have hM : I ≤ Module.annihilator R (IdealFiltration.Piece I J n) :=
    IdealFiltration.piece_annihilator I J n
  exact ResidueGenerators.value_le (I := I) (M := IdealFiltration.Piece I J n)
    (ι := Bounded h a n) hM ℓ (pieceGenerator z a n) (pieceGenerator_span z a n)

lemma sum_bounded_card (h a : ℕ) :
    ∑ n ∈ Finset.range (h*a+1), Fintype.card (Bounded h a n) = a ^ h := by
  have hh := Fintype.card_congr (boundedSigmaEquiv h a)
  rw [Fintype.card_sigma] at hh
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [Fintype.card_fun, Fintype.card_fin] using hh

lemma powers_contain_power (a : ℕ) :
    Ideal.span (Set.range z) ^ (h*a+1) ≤ Ideal.span (Set.range (fun i => z i ^ a)) := by
  have he : IsEmpty (Bounded h a (h*a+1)) := ⟨fun e => by
    have hh := bounded_degree_le a e.val
    rw [e.property] at hh
    omega⟩
  have hh := power_le_bounded_span z a (h*a+1)
  simpa only [Set.range_eq_empty, Ideal.span_empty, bot_sup_eq] using hh

end MonomialSpanning
end Lech


namespace Lech
universe u

lemma ennreal_finite_sum_saturated {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ≥0∞) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hg : ∀ i ∈ s, g i ≠ ⊤) (hs : ∑ i ∈ s, f i = ∑ i ∈ s, g i) :
    ∀ i ∈ s, f i = g i := by
  have hf : ∀ i ∈ s, f i ≠ ⊤ := fun i hi => ne_top_of_le_ne_top (hg i hi) (hfg i hi)
  have hr : ∑ i ∈ s, (f i).toReal = ∑ i ∈ s, (g i).toReal := by
    rw [← ENNReal.toReal_sum hf, ← ENNReal.toReal_sum hg, hs]
  have he := (Finset.sum_eq_sum_iff_of_le (fun i hi =>
    (ENNReal.toReal_le_toReal (hf i hi) (hg i hi)).mpr (hfg i hi))).mp hr
  intro i hi
  exact (ENNReal.toReal_eq_toReal_iff' (hf i hi) (hg i hi)).mp (he i hi)

variable {R : Type u} [CommRing R]
namespace TorsionLength
variable {I : Ideal R} (ℓ : TorsionLength I)
lemma kernel_zero_of_surjective_value_eq
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hM : powerTorsion I (ModuleCat.of R M))
    (hfin : ℓ.value (ModuleCat.of R N) ≠ ⊤)
    (he : ℓ.value (ModuleCat.of R M) = ℓ.value (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R f.ker) = 0 := by
  have hh := ℓ.additive_linear f.ker.subtype f f.ker.injective_subtype hf
    f.exact_subtype_ker_map hM
  rw [he] at hh
  exact (ENNReal.add_left_inj hfin).mp (hh.symm.trans (zero_add _).symm)
end TorsionLength

namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)
variable (ℓ : TorsionLength (Ideal.span (Set.range z)))

lemma piece_value_eq (a : ℕ)
    (hμ : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≠ ⊤)
    (ha : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
    (n : ℕ) (hn : n < h*a+1) :
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n)) =
      Fintype.card (Bounded h a n) •
        ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  apply ennreal_finite_sum_saturated (Finset.range (h*a+1))
      (fun n => ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z))
        (Ideal.span (Set.range (fun i => z i ^ a))) n)))
      (fun n => Fintype.card (Bounded h a n) •
        ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
  · intro i _
    exact piece_value_le z ℓ a i
  · intro i _
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ
  · rw [← IdealFiltration.length_quotient _ _ ℓ _ (powers_contain_power z a),
      Finset.sum_nsmul_assoc, sum_bounded_card, ha]
  · exact Finset.mem_range.mpr hn

end MonomialSpanning
end Lech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechBoundedEquiv
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
namespace Lech
universe u
variable {R : Type u} [CommRing R]
namespace MonomialSpanning

lemma bounded_card_of_lt (h a n : ℕ) (hn : n < a) :
    Fintype.card (Bounded h a n) = h.multichoose n := by
  have e := (boundedEquivTotal h a n hn).trans (Sym.equivNatSumOfFintype (Fin h) n).symm
  exact (Fintype.card_congr e).trans (Sym.card_sym_fin_eq_multichoose h n)

variable {h : ℕ} (z : Fin h → R)

lemma powers_le_power (a : ℕ) :
    Ideal.span (Set.range (fun i => z i ^ a)) ≤ Ideal.span (Set.range z) ^ a := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.pow_mem_pow (show z i ∈ Ideal.span (Set.range z) from
    Ideal.subset_span ⟨i, rfl⟩) a

lemma piece_value_eq_of_levels (ℓ : TorsionLength (Ideal.span (Set.range z)))
    (a n : ℕ) (hn : n < a) :
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n)) =
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z)) ⊥ n)) := by
  let I := Ideal.span (Set.range z)
  let J := Ideal.span (Set.range (fun i => z i ^ a))
  have hJ : J ≤ I ^ (n+1) := (powers_le_power z a).trans (Ideal.pow_le_pow_right hn)
  have h₁ : IdealFiltration.level I J n = IdealFiltration.level I ⊥ n := by
    simp only [IdealFiltration.level, sup_bot_eq]
    exact sup_eq_left.mpr (hJ.trans (Ideal.pow_le_pow_right (Nat.le_succ n)))
  have h₂ : IdealFiltration.level I J (n+1) = IdealFiltration.level I ⊥ (n+1) := by
    exact (sup_eq_left.mpr hJ).trans (sup_bot_eq _).symm
  exact congrArg₂ (fun (P Q : Ideal R) =>
    ℓ.value (ModuleCat.of R (P ⧸ Submodule.comap P.subtype Q))) h₁ h₂

lemma ordinary_piece_value (ℓ : TorsionLength (Ideal.span (Set.range z)))
    (hh : 0 < h)
    (hμ : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
    (n : ℕ) :
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z)) ⊥ n)) =
      h.multichoose n • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  rw [← piece_value_eq_of_levels z ℓ (n+1) n (Nat.lt_succ_self n)]
  have hn : n < h*(n+1)+1 := by nlinarith
  rw [piece_value_eq z ℓ (n+1) hμ (ha _ (Nat.succ_pos n)) n hn,
    bounded_card_of_lt _ _ _ (Nat.lt_succ_self n)]


end MonomialSpanning
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory


namespace Lech.Grading
open MvPolynomial
variable (S : Type*) [CommRing S]
lemma index_card (h n : ℕ) : Fintype.card (MonomialIndex h n) = h.multichoose n :=
  (Fintype.card_congr (indexEquiv h n)).trans (Sym.card_sym_fin_eq_multichoose h n)

end Lech.Grading

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PartialLaurent.laurentScalarTower _root_.OAI.Lech.PartialLaurent.polynomialLaurentAlgebra _root_.OAI.Lech.PartialLaurent.polynomialLaurentTower _root_.OAI.Lech.PartialLaurent.polynomialLocalization _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
namespace Lech
open CategoryTheory CategoryTheory.Limits MvPolynomial
universe u
variable {R : Type u} [CommRing R]
lemma torsion_of_quotient_scalar (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    powerTorsion I (ModuleCat.of R M) := by
  refine ⟨1, ?_⟩
  rw [pow_one]
  intro r hr
  rw [Module.mem_annihilator]
  intro m
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r m]
  change (Ideal.Quotient.mk I r) • m = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

namespace SourceGraded
variable (I : Ideal R) {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma degreeMap_surjective (n : ℕ) : Function.Surjective (degreeMap I z hz n) := by
  unfold degreeMap
  exact Homogeneous.gradedMap_surjective (R := R ⧸ I)
    (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I)
    (homogeneousSubmodule (Fin h) (R ⧸ I)) (IdealGraded.grade I)
    (IdealGraded.polynomialMap I z hz) (polynomialMap_smul I z hz)
    (IdealGraded.polynomialMap_surjective I z hz) n

variable (ell : TorsionLength I)
lemma polynomial_piece_value (h n : ℕ) :
    ell.value (ModuleCat.of R (homogeneousSubmodule (Fin h) (R ⧸ I) n)) =
      h.multichoose n • ell.value (ModuleCat.of R (R ⧸ I)) := by
  have ht := powerTorsion_pi_small (I := I) (M := R ⧸ I)
    (Grading.MonomialIndex h n) powerTorsion_quotient
  have e : homogeneousSubmodule (Fin h) (R ⧸ I) n ≃ₗ[R]
      (Grading.MonomialIndex h n → R ⧸ I) :=
    (Grading.homogeneousEquiv (R ⧸ I) h n).restrictScalars R
  have he := ell.value_linearEquiv (M := homogeneousSubmodule (Fin h) (R ⧸ I) n)
    (N := Grading.MonomialIndex h n → R ⧸ I) e ht
  exact he.trans ((ell.value_fintype_small powerTorsion_quotient
    (Grading.MonomialIndex h n)).trans (by rw [Grading.index_card]))

include hz in
lemma associated_piece_value
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (n : ℕ) :
    ell.value (ModuleCat.of R (IdealGraded.grade I n)) =
      h.multichoose n • ell.value (ModuleCat.of R (R ⧸ I)) := by
  have ht : powerTorsion I (ModuleCat.of R (IdealGraded.grade I n)) :=
    torsion_of_quotient_scalar I (IdealGraded.grade I n)
  have he := ell.value_linearEquiv (M := IdealGraded.Piece I n)
    (N := IdealGraded.grade I n) ((IdealGraded.pieceEquiv I n).restrictScalars R) ht
  rw [← he]
  subst I
  have hpiece := congrArg₂ (fun (P Q : Ideal R) =>
    ell.value (ModuleCat.of R (P ⧸ Submodule.comap P.subtype Q)))
    (sup_bot_eq (Ideal.span (Set.range z) ^ n))
    (sup_bot_eq (Ideal.span (Set.range z) ^ (n + 1)))
  exact hpiece.symm.trans (MonomialSpanning.ordinary_piece_value z ell hh hmu ha n)

attribute [local instance] OAI.Lech.SourceGraded.kernel_addCommGroup
attribute [local instance] OAI.Lech.SourceGraded.kernel_module
include hz in
 

lemma degree_kernel_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (n : ℕ) :
    ell.value (ModuleCat.of R ((degreeMap I z hz n).restrictScalars R).ker) = 0 := by
  apply ell.kernel_zero_of_surjective_value_eq
    (M := homogeneousSubmodule (Fin h) (R ⧸ I) n) (N := IdealGraded.grade I n)
    ((degreeMap I z hz n).restrictScalars R)
    (degreeMap_surjective I z hz n) (torsion_of_quotient_scalar I _)
  · rw [associated_piece_value I z hz ell hh hmu ha n, nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hmu
  · rw [polynomial_piece_value I ell h n, associated_piece_value I z hz ell hh hmu ha n]
end SourceGraded
end Lech

attribute [local instance] Classical.propDecidable


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))

lemma restrict_injective {s t : Finset (Fin h)} (hst : s ⊆ t) :
    Function.Injective (restrict R hst) :=
  mapDomain_injective (fun _ _ he => Subtype.ext
    (congrArg (fun e : exponents t => e.val) he))
end Lech.PartialLaurent

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PartialLaurentTotalDegree
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable


namespace Lech.ActualCech
open scoped BigOperators
universe u v
variable (A : Type u) [CommRing A] {ι : Type v}
lemma chosen_nonneg {h : ℕ} (hh : 0<h) {e : Fin h → ℤ} (he : 0≤∑ i,e i) :
    0 ≤ e (chosen hh e) := by
  dsimp [chosen]
  rw [dite_eq_left he]
  exact (exists_nonneg hh he).choose_spec

lemma contraction_mem {h n : ℕ} (hh : 0<h) {t : ℤ} (ht : 0≤t)
    {f : Cochains A h (n+1)} (hf : f ∈ homogeneous A h (n+1) t) :
    contraction A hh n f ∈ homogeneous A h n t := by
  intro e a he
  rw [contraction_apply]
  change f e (Fin.cons (chosen hh e) a) = 0
  apply hf
  by_cases het : (∑ i,e i) = t
  · right
    have hj : 0 ≤ e (chosen hh e) := chosen_nonneg hh (het.symm ▸ ht)
    have hna : ¬ Allowed e a := he.resolve_left (not_not.mpr het)
    intro hall
    apply hna
    intro i hi
    obtain ⟨k,hk⟩ := hall i hi
    revert hk
    refine Fin.cases ?_ (fun k => ?_) k
    · intro hk
      have : chosen hh e = i := by simpa using hk
      exact (not_lt_of_ge hj (this.symm ▸ hi)).elim
    · intro hk
      exact ⟨k,by simpa using hk⟩

  · exact Or.inl het

lemma contraction_identity {h : ℕ} (hh : 0<h) (n : ℕ) (f : Cochains A h (n+1)) :
    contraction A hh (n+1) (d A h (n+1) f) +
      d A h n (contraction A hh n f) = f := by
  apply Finsupp.ext
  intro e
  simp only [Finsupp.add_apply,contraction_apply,d_apply]
  exact extra_delta A (chosen hh e) n (f e)

 

theorem exact_nonnegative {h : ℕ} (hh : 0<h) (n : ℕ) {t : ℤ} (ht : 0≤t)
    (f : Cochains A h (n+1)) (hf : f ∈ homogeneous A h (n+1) t)
    (hc : d A h (n+1) f=0) :
    ∃ g ∈ homogeneous A h n t, d A h n g=f := by
  refine ⟨contraction A hh n f, contraction_mem A hh ht hf, ?_⟩
  have he := contraction_identity A hh n f
  simpa only [hc,map_zero,zero_add] using he
end Lech.ActualCech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ActualCechTranspose
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PartialLaurent.laurentScalarTower _root_.OAI.Lech.PartialLaurent.polynomialLaurentAlgebra _root_.OAI.Lech.PartialLaurent.polynomialLaurentTower _root_.OAI.Lech.PartialLaurent.polynomialLocalization _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.ActualCech

section
open scoped BigOperators
universe u
variable (A : Type u) [CommRing A]


theorem laurent_exact_nonnegative {h : ℕ} (hh : 0<h) (n : ℕ) {t : ℤ} (ht : 0≤t)
    (f : laurentCochains A h (n+1) t) (hf : laurentD A h (n+1) t f=0) :
    ∃ g : laurentCochains A h n t, laurentD A h n t g=f := by
  obtain ⟨x,rfl⟩ := (laurentEquiv A h (n+1) t).surjective f
  rw [laurentD_equiv] at hf
  have hc : d A h (n+1) x.val = 0 := by
    have hx := (laurentEquiv A h (n+2) t).injective (hf.trans (map_zero _).symm)
    exact congrArg Subtype.val hx
  obtain ⟨y,hy,hdy⟩ := exact_nonnegative A hh n ht x.val x.property hc
  refine ⟨laurentEquiv A h n t ⟨y,hy⟩, ?_⟩
  rw [laurentD_equiv]
  apply congrArg (laurentEquiv A h (n+1) t)
  exact Subtype.ext hdy
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
end Lech.ActualCech

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech

section


open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma quasiIsoAt_localization_iff {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι) :
    let Q := P.isoModSerre.Q
    let := ObjectProperty.SerreClassLocalization.abelian Q P
    let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
    let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
    QuasiIsoAt ((Q.mapHomologicalComplex c).map f) i ↔
      P.isoModSerre (HomologicalComplex.homologyMap f i) := by
  dsimp only
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  let S := K.sc i
  let T := L.sc i
  let g := (HomologicalComplex.shortComplexFunctor C c i).map f
  rw [quasiIsoAt_iff]
  change ShortComplex.QuasiIso (Q.mapShortComplex.map g) ↔ _
  rw [ShortComplex.quasiIso_iff]
  rw [← ObjectProperty.SerreClassLocalization.isIso_map_iff Q P]
  let h0 : (S.map Q).homology ⟶ (T.map Q).homology := ShortComplex.homologyMap (Q.mapShortComplex.map g)
  change IsIso h0 ↔ IsIso (Q.map (ShortComplex.homologyMap g))
  have he : h0 ≫ (T.mapHomologyIso Q).hom = (S.mapHomologyIso Q).hom ≫ Q.map (ShortComplex.homologyMap g) :=
    ShortComplex.mapHomologyIso_hom_naturality g Q
  have hfact : Q.map (ShortComplex.homologyMap g) =
      (S.mapHomologyIso Q).inv ≫ h0 ≫ (T.mapHomologyIso Q).hom := by
    rw [he, Iso.inv_hom_id_assoc]
  rw [hfact, isIso_comp_left_iff, isIso_comp_right_iff]


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
 

lemma homology_isoModSerre_of_termwise {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (hf : ∀ i, P.isoModSerre (f.f i)) (i : ι) :
    P.isoModSerre (homologyMap f i) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  have (j : ι) : IsIso (((Q.mapHomologicalComplex c).map f).f j) :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (f.f j)).mpr (hf j)
  have : IsIso ((Q.mapHomologicalComplex c).map f) := Hom.isIso_of_components _
  exact (quasiIsoAt_localization_iff P f i).mp inferInstance
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechPiIso
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech

section

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
universe u v w u' v'
variable {A : Type u'} [Category.{v'} A] [Abelian A]
lemma pi_isoModSerre (P : ObjectProperty A) [P.IsSerreClass]
    {ι : Type w} [Finite ι] {M N : ι → A} [HasProduct M] [HasProduct N]
    (f : ∀ i, M i ⟶ N i) (hf : ∀ i, P.isoModSerre (f i)) :
    P.isoModSerre (Limits.Pi.map f) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  have (i : ι) : IsIso (Q.map (f i)) :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (f i)).mpr (hf i)
  have he : Q.map (Limits.Pi.map f) ≫ piComparison Q N =
      piComparison Q M ≫ Limits.Pi.map (fun i => Q.map (f i)) := by
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
    rw [← Q.map_comp, Limits.Pi.map_π, Q.map_comp]
    rw [← Category.assoc, piComparison_comp_π]
  have : IsIso (Q.map (Limits.Pi.map f) ≫ piComparison Q N) := by
    rw [he]
    infer_instance
  have : IsIso (Q.map (Limits.Pi.map f)) := IsIso.of_isIso_comp_right _ (piComparison Q N)
  exact (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (Limits.Pi.map f)).mp inferInstance

end


open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Finite ι]
  {M N : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

omit [Finite ι] in
lemma piLinear_factorization :
    ModuleCat.ofHom (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      (ModuleCat.piIsoPi (fun i => ModuleCat.of R (M i))).inv ≫
      Limits.Pi.map (fun i => ModuleCat.ofHom (f i)) ≫
      (ModuleCat.piIsoPi (fun i => ModuleCat.of R (N i))).hom := by
  apply (cancel_mono (ModuleCat.piIsoPi (fun i => ModuleCat.of R (N i))).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Limits.Pi.hom_ext
  intro i
  simp only [Category.assoc,Limits.Pi.map_π,
    ModuleCat.piIsoPi_inv_kernel_ι]
  rw [← Category.assoc, ModuleCat.piIsoPi_inv_kernel_ι]
  rfl

lemma piLinear_isoModSerre (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hf : ∀ i, P.isoModSerre (ModuleCat.ofHom (f i))) :
    P.isoModSerre (ModuleCat.ofHom (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i)))) := by
  rw [piLinear_factorization]
  exact P.isoModSerre.comp_mem _ _
    (P.isoModSerre_of_isIso _)
    (P.isoModSerre.comp_mem _ _ (pi_isoModSerre P _ hf) (P.isoModSerre_of_isIso _))

lemma isoModSerre_of_surjective_kernel
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (hsurj : Function.Surjective f) (hk : P (ModuleCat.of R f.ker)) :
    P.isoModSerre (ModuleCat.ofHom f) := by
  have : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hsurj
  rw [P.isoModSerre_iff_of_epi]
  exact (P.prop_iff_of_iso (ModuleCat.kernelIsoKer (ModuleCat.ofHom f))).mpr hk
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
lemma homology_zeroClass_of_termwise_exactAt {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (hf : ∀ i, P.isoModSerre (f.f i)) (i : ι) (hi : K.ExactAt i) :
    P (L.homology i) := by
  have h := (homology_isoModSerre_of_termwise P f hf i).2
  have hz := (exactAt_iff_isZero_homology K i).mp hi
  have he := hz.eq_of_src (homologyMap f i) 0
  rw [he,P.epiModSerre_zero_iff] at h
  exact h
end Lech


namespace Lech.TwistedLocalization

section

section
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)


include hf

omit hf
variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)


include hf

omit [GradedAlgebra H] in
lemma iSup_range_kernelFraction (t : ℕ) :
    (⨆ n, LinearMap.range (kernelFraction G hf H g hg t n)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n,a,ha⟩ := kernel_fraction G hf H g hg t x
  exact Submodule.mem_iSup_of_mem n ⟨a,Subtype.ext ha⟩

open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] pieceMap gradedMap kernelFraction
attribute [local instance] OAI.Lech.TwistedLocalization.kernelAdd
attribute [local instance] OAI.Lech.TwistedLocalization.kernelModule
omit [GradedAlgebra H] in
 

theorem kernel_property (t : ℕ) (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hker : ∀ n, P (ModuleCat.of R (LinearMap.ker (gradedMap G H g hg n))))
    (hsum : ∀ (U : ℕ → Submodule R (LinearMap.ker (pieceMap G hf H g hg t))),
      (∀ n, P (ModuleCat.of R ↥(U n))) →
        P (ModuleCat.of R ↥(⨆ n,U n : Submodule R (LinearMap.ker (pieceMap G hf H g hg t))))) :
    P (ModuleCat.of R (LinearMap.ker (pieceMap G hf H g hg t))) := by
  let U (n : ℕ) := LinearMap.range (kernelFraction G hf H g hg t n)
  have hU (n : ℕ) : P (ModuleCat.of R ↥(U n)) := by
    let q : ModuleCat.of R (LinearMap.ker (gradedMap G H g hg (n*d+t))) ⟶
        ModuleCat.of R (U n) := ModuleCat.ofHom (kernelFraction G hf H g hg t n).rangeRestrict
    let : Epi q := (ModuleCat.epi_iff_surjective q).mpr
      (by rintro ⟨y,a,rfl⟩; exact ⟨a,rfl⟩)
    exact P.prop_of_epi q (hker (n*d+t))
  have hu := hsum U hU
  have he : (⨆ n,U n) = ⊤ := iSup_range_kernelFraction G hf H g hg t
  have hu' : P (ModuleCat.of R (⊤ : Submodule R (LinearMap.ker (pieceMap G hf H g hg t)))) :=
    he ▸ hu
  exact P.prop_of_iso (LinearEquiv.ofTop (⊤ : Submodule R
    (LinearMap.ker (pieceMap G hf H g hg t))) rfl).toModuleIso hu'

end


open SetLike Graded
universe u

end


open SetLike Graded
universe u

end Lech.TwistedLocalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.PartialLaurent
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma polynomial_exact {h : ℕ} (hh : 0<h) (n t : ℕ)
    (f : polynomialCochains R h (n+1) t) (hf : polynomialD R h (n+1) t f=0) :
    ∃ g : polynomialCochains R h n t, polynomialD R h n t g=f := by
  have hl : ActualCech.laurentD R h (n+1) (t : ℤ)
      (polynomialCochainsEquiv R h (n+1) t f)=0 := by
    rw [←polynomialCochainsEquiv_d,hf,map_zero]
  obtain ⟨x,hx⟩ := ActualCech.laurent_exact_nonnegative R hh n (Int.natCast_nonneg t) _ hl
  refine ⟨(polynomialCochainsEquiv R h n t).symm x,?_⟩
  apply (polynomialCochainsEquiv R h (n+1) t).injective
  rw [polynomialCochainsEquiv_d,LinearEquiv.apply_symm_apply,hx]

end Lech.PartialLaurent


namespace Lech.RestrictedPolynomialCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma exact {h : ℕ} (hh : 0<h) (n t : ℕ)
    (f : cochains R S h (n+1) t) (hf : d R S h (n+1) t f=0) :
    ∃ g : cochains R S h n t, d R S h n t g=f := by
  have hl : PartialLaurent.polynomialD S h (n+1) t
      (cochainsEquiv R S h (n+1) t f)=0 := by rw [←cochainsEquiv_d,hf,map_zero]
  obtain ⟨x,hx⟩ := PartialLaurent.polynomial_exact S hh n t _ hl
  refine ⟨(cochainsEquiv R S h n t).symm x,?_⟩
  apply (cochainsEquiv R S h (n+1) t).injective
  rw [cochainsEquiv_d,LinearEquiv.apply_symm_apply,hx]

lemma exactAt {h : ℕ} (hh : 0<h) (n t : ℕ) :
    (complex R S h t).ExactAt (n+1) := by
  apply ((complex R S h t).exactAt_iff' (i := n) (j := n+1) (k := n+2)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change (CochainComplex.of.d
    (fun n => ModuleCat.of R (cochains R S h n t))
    (fun n => ModuleCat.ofHom (d R S h n t)) (n+1) ((n+1)+1)).hom f=0 at hf
  rw [CochainComplex.of_d] at hf
  obtain ⟨x,hx⟩ := exact R S hh n t f hf
  refine ⟨x,?_⟩
  change (CochainComplex.of.d
    (fun n => ModuleCat.of R (cochains R S h n t))
    (fun n => ModuleCat.ofHom (d R S h n t)) n (n+1)).hom x=f
  rw [CochainComplex.of_d]
  exact hx
end Lech.RestrictedPolynomialCech


namespace Lech.ActualCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (A : Type u) [CommRing A]

lemma laurentD_zero_injective {h : ℕ} (hh : 0<h) (t : ℤ) :
    Function.Injective (laurentD A h 0 t) := by
  intro x y hxy
  funext a
  let u : Fin 1 → Fin h := fun _ => ⟨0,hh⟩
  have he := congrFun hxy u
  change (∑ i : Fin 1, (-1 : A)^i.val •
    PartialLaurent.coefficientChartRestrict A (intersection_delete u i) t
      (x (u ∘ i.succAbove))) = (∑ i : Fin 1, (-1 : A)^i.val •
    PartialLaurent.coefficientChartRestrict A (intersection_delete u i) t
      (y (u ∘ i.succAbove))) at he
  simp only [Fin.sum_univ_one,Fin.val_zero,pow_zero,one_smul] at he
  have hae : (u ∘ (0 : Fin 1).succAbove) = a := Subsingleton.elim _ _
  subst a
  apply Subtype.ext
  exact PartialLaurent.restrict_injective A (intersection_delete u 0)
    (congrArg Subtype.val he)
end Lech.ActualCech


namespace Lech.PartialLaurent
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
lemma polynomialD_zero_injective {h : ℕ} (hh : 0<h) (t : ℕ) :
    Function.Injective (polynomialD R h 0 t) := by
  intro x y hxy
  apply (polynomialCochainsEquiv R h 0 t).injective
  apply ActualCech.laurentD_zero_injective R hh (t : ℤ)
  rw [←polynomialCochainsEquiv_d,←polynomialCochainsEquiv_d,hxy]
end Lech.PartialLaurent


namespace Lech.RestrictedPolynomialCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.gradedAlgebra
lemma d_zero_injective {h : ℕ} (hh : 0<h) (t : ℕ) :
    Function.Injective (d R S h 0 t) := by
  intro x y hxy
  apply (cochainsEquiv R S h 0 t).injective
  apply PartialLaurent.polynomialD_zero_injective S hh t
  rw [←cochainsEquiv_d,←cochainsEquiv_d,hxy]

lemma exactAt_zero {h : ℕ} (hh : 0<h) (t : ℕ) :
    (complex R S h t).ExactAt 0 := by
  apply ((complex R S h t).exactAt_iff' (i := 0) (j := 0) (k := 1)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change (CochainComplex.of.d
    (fun n => ModuleCat.of R (cochains R S h n t))
    (fun n => ModuleCat.ofHom (d R S h n t)) 0 (0+1)).hom f=0 at hf
  rw [CochainComplex.of_d] at hf
  have hfz : f=0 := d_zero_injective R S hh t (hf.trans (map_zero _).symm)
  refine ⟨0,?_⟩
  simpa only [map_zero] using hfz.symm

lemma exactAt_all {h : ℕ} (hh : 0<h) (n t : ℕ) :
    (complex R S h t).ExactAt n := by
  cases n with
  | zero => exact exactAt_zero R S hh t
  | succ n => exact exactAt R S hh n t
end Lech.RestrictedPolynomialCech


namespace Lech.RestrictedPolynomialImageCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {h : ℕ} (H : ℕ → Submodule R B) [GradedAlgebra H]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (g : (RestrictedPolynomialCech.grade R S h) →+*ᵍ H)
  (hg : ∀ (r : R) (a : MvPolynomial (Fin h) S), g (r • a) = r • g a)

lemma comparison_f (hsurj : Function.Surjective g) (t n : ℕ) :
    (comparison H g hg hsurj t).f n = ModuleCat.ofHom (mapCochains H g hg n t) := rfl

lemma comparison_termwise (hsurj : Function.Surjective g)
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] (t : ℕ)
    (hk : ∀ s : Finset (Fin h), P (ModuleCat.of R
      (ImageCech.mapTerm (RestrictedPolynomialCech.grade R S h) H g hg
        MvPolynomial.X (MvPolynomial.isHomogeneous_X S) s t).ker)) (n : ℕ) :
    P.isoModSerre ((comparison H g hg hsurj t).f n) := by
  rw [comparison_f]
  apply piLinear_isoModSerre
  intro a
  apply isoModSerre_of_surjective_kernel
  · exact ImageCech.mapTerm_surjective _ _ _ _ _ _ hsurj _ _
  · exact hk _
end Lech.RestrictedPolynomialImageCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RestrictedPolynomialImageCechComparisonHomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.RestrictedPolynomialImageCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {h : ℕ} (H : ℕ → Submodule R B) [GradedAlgebra H]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (g : (RestrictedPolynomialCech.grade R S h) →+*ᵍ H)
  (hg : ∀ (r : R) (a : MvPolynomial (Fin h) S), g (r • a) = r • g a)
  (hsurj : Function.Surjective g) (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
  (t : ℕ)
  (hk : ∀ s : Finset (Fin h), P (ModuleCat.of R
      (ImageCech.mapTerm (RestrictedPolynomialCech.grade R S h) H g hg
        MvPolynomial.X (MvPolynomial.isHomogeneous_X S) s t).ker))

include hk in
lemma homology_mem (hh : 0<h) (n : ℕ) : P ((complex H g hg hsurj t).homology n) :=
  homology_zeroClass_of_termwise_exactAt P _
    (comparison_termwise H g hg hsurj P t hk) n
    (RestrictedPolynomialCech.exactAt_all R S hh n t)
end Lech.RestrictedPolynomialImageCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominator
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.FilteredFraction


open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)


lemma quotientGraded_surjective : Function.Surjective (quotientGraded I) :=
  Ideal.Quotient.mk_surjective

attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap quotientGraded
attribute [local instance] TwistedLocalization.kernelAdd TwistedLocalization.kernelModule

lemma quotientTwist_surjective (t : ℕ) : Function.Surjective (quotientTwist I hw t) := by
  unfold quotientTwist
  apply TwistedLocalization.pieceMap_surjective
  exact quotientGraded_surjective I

lemma layerMap_surjective (t : ℕ) : Function.Surjective (layerMap I hw t) :=
  (quotientTwist_surjective I hw t).comp (reesEquiv I hw t).symm.surjective

end Lech.FilteredFraction


namespace Lech.SourceGraded
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

attribute [local irreducible] TwistedLocalization.piece FilteredFraction.quotientGraded


lemma filteredReduction_surjective (s : Finset (Fin h)) (t : ℕ) :
    Function.Surjective (filteredReduction I z hz s t) :=
  (exceptionalTermEquiv I z hz s t).surjective.comp
    (FilteredFraction.layerMap_surjective I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t)

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

lemma inclusion_refl (t : ℕ) : inclusion I z hz (le_refl t)=𝟙 (complex I z hz t) := by
  ext n x
  rfl

end Lech.FilteredCech

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

 

lemma cokernel_comp_shortExact {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    (kernelCokernelCompSequence.snakeInput f g).L₃.ShortExact where
  exact := (kernelCokernelCompSequence.snakeInput f g).L₃_exact
  mono_f := (kernelCokernelCompSequence.snakeInput f g).L₂'_exact.mono_g
    ((isZero_kernel_of_mono g).eq_of_src _ _)
  epi_g := by
    change Epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))
    infer_instance



lemma cokernel_homology_property_of_shortExact {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i : ι)
    (h : P (S.X₃.homology i)) : P ((cokernel S.f).homology i) :=
  P.prop_of_iso ((homologyFunctor C c i).mapIso (cokernelIsoOfShortExact hS)).symm h

 

lemma homology_middle_property {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i : ι)
    (h₁ : P (S.X₁.homology i)) (h₃ : P (S.X₃.homology i)) : P (S.X₂.homology i) :=
  P.prop_X₂_of_exact (hS.homology_exact₂ i) h₁ h₃

 

lemma cokernel_comp_homology_property {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L M : HomologicalComplex C c} (f : K ⟶ L) (g : L ⟶ M) [Mono g]
    (i : ι) (hf : P ((cokernel f).homology i)) (hg : P ((cokernel g).homology i)) :
    P ((cokernel (f ≫ g)).homology i) :=
  homology_middle_property P (cokernel_comp_shortExact f g) i hf hg
end Lech


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece FilteredFraction.piece IdealGraded.polynomialMap


lemma filteredReductionCochains_surjective (n t : ℕ) :
    Function.Surjective (filteredReductionCochains I z hz n t) := by
  intro x
  choose y hy using fun a => filteredReduction_surjective I z hz
    (ActualCech.intersection a) t (x a)
  exact ⟨y,funext hy⟩

lemma filteredLayerSequence_shortExact (t : ℕ) : (filteredLayerSequence I z hz t).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · apply LinearMap.exact_iff.mpr
    exact filteredReductionCochains_kernel I z hz n t
  · exact LocalizationCech.inclusionLinear_injective z (FilteredCech.term I z (t+1))
      (FilteredCech.term I z t) (fun _ => FilteredFraction.antitone I _ _ (Nat.le_succ t)) n
  · exact filteredReductionCochains_surjective I z hz n t
end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionZeroStability
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}


namespace TorsionLength
variable (ell : TorsionLength I)

lemma zero_of_surjective_torsion {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hT : powerTorsion I (ModuleCat.of R M)) (hM : ell.value (ModuleCat.of R M)=0) :
    ell.value (ModuleCat.of R N)=0 := by
  let : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  exact le_antisymm ((ell.le_of_epi (ModuleCat.ofHom f) hT).trans_eq hM) bot_le



lemma iSup_zero_torsion (hds : ell.DirectSumZero) {ι M : Type u}
    [AddCommGroup M] [Module R M] (U : ι → Submodule R M)
    (hT : powerTorsion I (ModuleCat.of R M))
    (hU : ∀ i, ell.value (ModuleCat.of R (U i))=0) :
    ell.value (ModuleCat.of R (⨆ i,U i : Submodule R M))=0 := by
  classical
  obtain ⟨a,ha⟩ := hT
  have hUa : ∀ i, I^a ≤ Module.annihilator R (U i) := fun i =>
    ha.trans ((U i).subtype.annihilator_le_of_injective (U i).injective_subtype)
  have hsum : powerTorsion I (ModuleCat.of R (⨁ i,U i)) := by
    refine ⟨a,?_⟩
    change I^a ≤ Module.annihilator R (Π₀ i, U i)
    rw [Module.annihilator_dfinsupp]
    exact le_iInf hUa
  have hh := ell.zero_of_surjective_torsion (DirectSum.coeLinearMap U).rangeRestrict
    (DirectSum.coeLinearMap U).surjective_rangeRestrict hsum (hds (fun i => U i) a hUa hU)
  rwa [DirectSum.range_coeLinearMap] at hh

end TorsionLength
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionChartKernel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
lemma powerTorsion_submodule {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hT : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R N) := by
  obtain ⟨a,ha⟩ := hT
  exact ⟨a,ha.trans (N.subtype.annihilator_le_of_injective N.injective_subtype)⟩
end Lech

namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z)=I) (ell : TorsionLength I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.SourceGraded.torsionGradedKernelAdd
attribute [local instance] OAI.Lech.SourceGraded.torsionGradedKernelModule
attribute [local instance] OAI.Lech.SourceGraded.degreeKernelAdd
attribute [local instance] OAI.Lech.SourceGraded.degreeKernelModule
include hz in
lemma mapR_degree_kernel_zero_torsion
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^h • ell.value (ModuleCat.of R (R ⧸ I))) (n : ℕ) :
    ell.value (ModuleCat.of R (gradedMapR I z hz n).ker)=0 := by
  let e : (gradedMapR I z hz n).ker ≃ₗ[R]
      ((degreeMap I z hz n).restrictScalars R).ker :=
    { toFun := fun x => ⟨⟨x.val.val,by simpa only [sourceGrade,Submodule.restrictScalars_mem] using x.val.property⟩,by
        apply Subtype.ext
        have hx := congrArg Subtype.val (LinearMap.mem_ker.mp x.property)
        change IdealGraded.polynomialMap I z hz x.val.val=0 at hx ⊢
        exact hx⟩
      invFun := fun x => ⟨⟨x.val.val,by simpa only [sourceGrade,Submodule.restrictScalars_mem] using x.val.property⟩,by
        apply Subtype.ext
        have hx := congrArg Subtype.val (LinearMap.mem_ker.mp x.property)
        change IdealGraded.polynomialMap I z hz x.val.val=0 at hx ⊢
        exact hx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT := powerTorsion_submodule I ((degreeMap I z hz n).restrictScalars R).ker
    (torsion_of_quotient_scalar I (homogeneousSubmodule (Fin h) (R ⧸ I) n))
  exact (ell.value_linearEquiv e hT).trans (degree_kernel_zero I z hz ell hh hmu ha n)

end Lech.SourceGraded

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionThickening
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TwistedLocalization
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)

include hf in
lemma piece_torsion (I : Ideal R) (hT : powerTorsion I (ModuleCat.of R A)) (t : ℕ) :
    powerTorsion I (ModuleCat.of R (piece G (f:=f) (d:=d) t)) := by
  obtain ⟨a,ha⟩ := hT
  refine ⟨a,?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  obtain ⟨n,b,hb⟩ := exists_fraction G hf t x
  change r • (x : Localization.Away f)=0
  rw [←hb,←map_smul]
  have hz : r • b=0 := Subtype.ext (Module.mem_annihilator.mp (ha hr) b)
  rw [hz,map_zero]

variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A),g (r • a)=r • g a)
  (I : Ideal R) (ell : TorsionLength I)

attribute [local instance] kernelAdd kernelModule
attribute [local irreducible] pieceMap gradedMap kernelFraction
omit [GradedAlgebra H] in
include hf in
lemma kernel_zeroClass (hds : ell.DirectSumZero)
    (hT : powerTorsion I (ModuleCat.of R A))
    (hker : ∀ n,ell.value (ModuleCat.of R (Homogeneous.gradedMap G H g hg n).ker)=0) (t : ℕ) :
    ell.zeroClass (ModuleCat.of R (pieceMap G hf H g hg t).ker) := by
  have htK : powerTorsion I (ModuleCat.of R (pieceMap G hf H g hg t).ker) :=
    powerTorsion_submodule I _ (piece_torsion G hf I hT t)
  apply kernel_property G hf H g hg t ell.zeroClass
  · intro n
    exact ell.zeroClass.prop_of_iso (gradedKernelEquiv G H g hg n).symm.toModuleIso
      ⟨powerTorsion_submodule I _ (powerTorsion_submodule I (G n) hT),hker n⟩
  · intro U hU
    refine ⟨powerTorsion_submodule I _ htK,?_⟩
    have hh := ell.iSup_zero_torsion hds (fun n : ULift.{u} ℕ => U n.down) htK
      (fun n => (hU n.down).2)
    have he : (⨆ n : ULift.{u} ℕ,U n.down) = ⨆ n : ℕ,U n := by
      simp only [iSup_ulift]
    rw [he] at hh
    exact hh
end Lech.TwistedLocalization

namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I) (ell : TorsionLength I)
  (hds : ell.DirectSumZero) (hh : 0<h)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value
    (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
      a^h • ell.value (ModuleCat.of R (R ⧸ I)))
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap
  TwistedLocalization.gradedMap ImageCech.mapTerm IdealGraded.polynomialMap

include hz hds hh hmu ha in
lemma twist_kernel_zeroClass
    {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ} (hf : f∈sourceGrade I h d) (t : ℕ) :
    ell.zeroClass (ModuleCat.of R (twistMapR I z hz hf t).ker) := by
  unfold twistMapR
  apply TwistedLocalization.kernel_zeroClass _ hf _ _ _ I ell hds
    (torsion_of_quotient_scalar I (MvPolynomial (Fin h) (R ⧸ I)))
  exact mapR_degree_kernel_zero_torsion I z hz ell hh hmu ha

include hz hds hh hmu ha in
lemma exceptionalCech_homology_zeroClass (t n : ℕ) :
    ell.zeroClass ((exceptionalCech I z hz t).homology n) := by
  apply RestrictedPolynomialImageCech.homology_mem (R:=R) (S:=R ⧸ I) (B:=IdealGraded.Ring I)
    (targetGrade I) (mapR I z hz) (mapR_smul I z hz) (mapR_surjective I z hz) ell.zeroClass t _ hh n
  intro s
  unfold ImageCech.mapTerm
  exact twist_kernel_zeroClass I z hz ell hds hh hmu ha
    (GradedChart.denominator_mem (sourceGrade I h) MvPolynomial.X
      (MvPolynomial.isHomogeneous_X (R ⧸ I)) s) t

include hds hh hmu ha in
lemma finiteThickening_homology_zeroClass_oai (t M n : ℕ) :
    ell.zeroClass ((finiteThickening I z hz t M).homology n) := by
  induction M with
  | zero =>
      have hi : Epi (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t 0)) := by
        simpa only [FilteredCech.inclusion_refl] using
          (inferInstance : Epi (𝟙 (FilteredCech.complex I z (coordinate_mem I z hz) t)))
      unfold finiteThickening
      exact ell.zeroClass.prop_of_isZero
        ((homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map_isZero
          (isZero_cokernel_of_epi (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t 0))))
  | succ M ih =>
      have hl := cokernel_homology_property_of_shortExact ell.zeroClass
        (filteredLayerSequence_shortExact I z hz (t+M)) n
        (exceptionalCech_homology_zeroClass I z hz ell hds hh hmu ha (t+M) n)
      have hc := cokernel_comp_homology_property ell.zeroClass
        (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_succ (t+M)))
        (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t M)) n hl ih
      rw [FilteredCech.inclusion_comp] at hc
      exact hc

end Lech.SourceGraded

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass_oai.{u} := @OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass_oai.{u}
