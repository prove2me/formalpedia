-- Prove2me | solution 1 for OAI.Lech.PowerSeries.maximal_power_colength
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:13:22.531965+00:00
-- url     : https://prove2.me/submissions/a047288f-4dda-4fba-8ca6-babef306637e

import Mathlib
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L021
import Definitions.Def_OAIQ032L023

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

 
lemma power_colength (ℓ : TorsionLength (Ideal.span (Set.range z)))
    (hh : 0 < h)
    (hμ : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
    (M : ℕ) (hM : 0 < M) :
    ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z) ^ M)) =
      (M+h-1).choose h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  have he := IdealFiltration.length_eq_sum (Ideal.span (Set.range z)) ⊥ ℓ M
  have hlev : IdealFiltration.level (Ideal.span (Set.range z)) ⊥ M =
      Ideal.span (Set.range z) ^ M := sup_bot_eq _
  have hv := congrArg (fun J : Ideal R => ℓ.value (ModuleCat.of R (R ⧸ J))) hlev
  rw [← hv, he]
  simp_rw [ordinary_piece_value z ℓ hh hμ ha]
  rw [Finset.sum_nsmul_assoc]
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  rw [Nat.sum_range_multichoose]
  congr 2
  omega

end MonomialSpanning
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors

open scoped nonZeroDivisors


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma pick_zero : pick (0 : σ →₀ ℕ) = none := by simp [pick]
lemma pick_positive {d : σ →₀ ℕ} {i : σ} (hi : pick d = some i) : 0 < d i := by
  classical
  by_cases hd : d = 0
  · subst d; simp [pick] at hi
  · have hc : Classical.choose (exists_positive hd) = i := by
      exact Option.some.inj (by simpa only [pick,dite_eq_right hd] using hi)
    rw [← hc]
    exact Classical.choose_spec (exists_positive hd)

lemma exists_pick {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, pick d = some i := by
  simp [pick,hd]

lemma coeff_divide_X (f : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (divide f i * X i) = if pick d = some i then coeff d f else 0 := by
  classical
  rw [X,coeff_mul_monomial]
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hle]
    simp only [mul_one]
    change (if pick (d - Finsupp.single i 1 + Finsupp.single i 1) = some i then
      coeff (d - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
    rw [tsub_add_cancel_of_le hle]
  · rw [ite_eq_right hle]
    have hp : pick d ≠ some i := by
      intro hc
      apply hle
      intro j
      by_cases hji : j = i
      · subst j; simpa using (Nat.succ_le_iff.mpr (pick_positive hc))
      · simp [hji]
    simp [hp]

 

lemma sum_divide_X (f : MvPowerSeries σ R) :
    ∑ i, divide f i * X i = f - C (constantCoeff f) := by
  classical
  ext d
  simp only [map_sum,coeff_divide_X,map_sub]
  by_cases hd : d = 0
  · subst d
    simp [pick_zero]
  · obtain ⟨i,hi⟩ := exists_pick hd
    rw [Finset.sum_eq_single i]
    · simp [hi,coeff_C,hd]
    · intro j _ hji
      simp [hi,Ne.symm hji]
    · simp

lemma variables_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro f hf
    have hc : constantCoeff f = 0 := hf
    have h := sum_divide_X f
    rw [hc,map_zero,sub_zero] at h
    rw [← h]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

variable {k : Type*} [Field k]
lemma maximalIdeal_eq_variables :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) := by
  rw [variables_eq_ker_constantCoeff]
  ext f
  simp only [IsLocalRing.mem_maximalIdeal,RingHom.mem_ker,mem_nonunits_iff,isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero,not_not]

end Lech.PowerSeries


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

open CategoryTheory


namespace Lech.RootTower
open MvPowerSeries IsLocalRing
variable {σ k : Type*} [Fintype σ] [Field k] (q : ℕ) [NeZero q]

omit [Fintype σ] in
lemma expansion_residue_surjective : Function.Surjective
    (ResidueField.map (algebraMap (MvPowerSeries σ k) (Expanded (σ := σ) (R := k) q))) := by
  intro x
  obtain ⟨f,rfl⟩ := residue_surjective x
  refine ⟨residue (MvPowerSeries σ k) (C (constantCoeff f)), ?_⟩
  rw [ResidueField.map_residue]
  change residue (MvPowerSeries σ k) (expand q (NeZero.ne q) (C (constantCoeff f))) = _
  rw [expand_C]
  exact (residue_eq_constant f).symm

lemma variable_powers_colength :
    Module.length (MvPowerSeries σ k)
      (MvPowerSeries σ k ⧸ Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ k)^q))) =
      (q ^ Fintype.card σ : ℕ) := by
  have hid : (maximalIdeal (MvPowerSeries σ k)).map
      (expand (σ := σ) (R := k) q (NeZero.ne q)).toRingHom =
      Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ k)^q)) := by
    rw [Lech.PowerSeries.maximalIdeal_eq_variables, Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact MvPowerSeries.expand_X q (NeZero.ne q) i
  have h := fiber_length_of_basis (expansionBasis (σ := σ) (R := k) q)
    (expansion_residue_surjective (σ := σ) (k := k) q)
  change Module.length (MvPowerSeries σ k) (MvPowerSeries σ k ⧸
    (maximalIdeal (MvPowerSeries σ k)).map
      (expand q (NeZero.ne q)).toRingHom) = _ at h
  rw [hid] at h
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

end Lech.RootTower


namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing
variable {k : Type*} [Field k] (h : ℕ)

lemma maximal_power_colength_oai (hh : 0 < h) (N : ℕ) (hN : 0 < N) :
    Module.length (MvPowerSeries (Fin h) k)
      (MvPowerSeries (Fin h) k ⧸ maximalIdeal (MvPowerSeries (Fin h) k)^N) =
      ((N+h-1).choose h : ℕ) := by
  let R := MvPowerSeries (Fin h) k
  let z : Fin h → R := X
  have hm : Ideal.span (Set.range z) = maximalIdeal R := maximalIdeal_eq_variables.symm
  have hμ : (ordinaryLength (Ideal.span (Set.range z))).value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) = 1 := by
    change (Module.length R (R ⧸ Ideal.span (Set.range z))).toENNReal = 1
    let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    rw [hm, Module.length_eq_of_surjective (R := R ⧸ maximalIdeal R)
      Ideal.Quotient.mk_surjective]
    rw [Module.length_eq_one]
    simp
  have ha (a : ℕ) (ha : 0 < a) :
      (ordinaryLength (Ideal.span (Set.range z))).value
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
        a ^ h • (ordinaryLength (Ideal.span (Set.range z))).value
          (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
    let : NeZero a := ⟨ha.ne'⟩
    rw [hμ]
    change (Module.length R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))).toENNReal = _
    rw [RootTower.variable_powers_colength]
    simp
  have H := MonomialSpanning.power_colength z (ordinaryLength _) hh
    (by rw [hμ]; exact ENNReal.one_ne_top) ha N hN
  rw [hμ,nsmul_eq_mul,mul_one] at H
  change (Module.length R (R ⧸ Ideal.span (Set.range z)^N)).toENNReal = _ at H
  rw [hm] at H
  exact ENat.toENNReal_inj.mp (by simpa using H)
end Lech.PowerSeries


end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Lech.PowerSeries.maximal_power_colength_oai.{u_1} := @OAI.Lech.PowerSeries.maximal_power_colength_oai.{u_1}
