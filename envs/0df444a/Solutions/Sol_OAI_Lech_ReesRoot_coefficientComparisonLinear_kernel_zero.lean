-- Prove2me | solution 1 for OAI.Lech.ReesRoot.coefficientComparisonLinear_kernel_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:37:09.56658+00:00
-- url     : https://prove2.me/submissions/ab62bff7-ca04-406c-8d13-ea2c9a2a4082

import Mathlib
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


namespace Lech.Homogeneous

section
open HomogeneousLocalization SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]


variable (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)


lemma kernel_fraction {f : A} {d : ℕ} (hf : f ∈ G d)
    (x : LinearMap.ker (awayMap G H g hg f)) :
    ∃ (n : ℕ) (a : LinearMap.ker (gradedMap G H g hg (n*d))),
      fraction G hf n a = (x : Away G f) := by
  obtain ⟨n,a,ha,hax⟩ := Away.mk_surjective G hf x
  have hz := x.2
  change awayMap G H g hg f x = 0 at hz
  rw [←hax] at hz
  change Away.map g f (Away.mk G hf n a ha) = 0 at hz
  rw [Away.map_mk] at hz
  have hv := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk,val_zero,Localization.mk_eq_mk'] at hv
  obtain ⟨⟨s,hs⟩,he⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hv
  obtain ⟨k,rfl⟩ := hs
  have hmem : f^k*a ∈ G ((k+n)*d) := by
    rw [add_mul]
    exact mul_mem_graded (by simpa only [nsmul_eq_mul,Nat.cast_id] using
      (pow_mem_graded k hf)) (by simpa only [nsmul_eq_mul,Nat.cast_id] using ha)
  have hker : gradedMap G H g hg ((k+n)*d) ⟨f^k*a,hmem⟩ = 0 := by
    apply Subtype.ext
    change g (f^k*a) = 0
    simpa only [map_mul,map_pow] using he
  refine ⟨k+n,⟨⟨f^k*a,hmem⟩,hker⟩,?_⟩
  rw [← hax]
  apply val_injective (Submonoid.powers f)
  simp only [fraction,LinearMap.coe_mk,AddHom.coe_mk,Away.val_mk]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

end


open HomogeneousLocalization SetLike Graded
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {f : A} {d : ℕ} (hf : f ∈ G d)

lemma iSup_range_kernelFraction :
    (⨆ n, LinearMap.range (kernelFraction G H g hg hf n)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n,a,ha⟩ := kernel_fraction G H g hg hf x
  apply Submodule.mem_iSup_of_mem n
  exact ⟨a,Subtype.ext ha⟩

attribute [local instance] OAI.Lech.Homogeneous.awayAddCommGroup
include hf in
 

theorem kernel_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hker : ∀ n, P (ModuleCat.of R (LinearMap.ker (gradedMap G H g hg n))))
    (hsum : ∀ (U : ℕ → Submodule R (LinearMap.ker (awayMap G H g hg f))),
      (∀ n, P (ModuleCat.of R ↥(U n))) → P (ModuleCat.of R ↥(⨆ n,U n : Submodule R (LinearMap.ker (awayMap G H g hg f))))) :
    P (ModuleCat.of R (LinearMap.ker (awayMap G H g hg f))) := by
  let U (n : ℕ) := LinearMap.range (kernelFraction G H g hg hf n)
  have hU (n : ℕ) : P (ModuleCat.of R ↥(U n)) := by
    let q : ModuleCat.of R (LinearMap.ker (gradedMap G H g hg (n*d))) ⟶
        ModuleCat.of R (U n) :=
      ModuleCat.ofHom (kernelFraction G H g hg hf n).rangeRestrict
    let : Epi q := (ModuleCat.epi_iff_surjective q).mpr
      (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
    exact P.prop_of_epi q (hker (n*d))
  have hu := hsum U hU
  have he : (⨆ n,U n) = ⊤ := iSup_range_kernelFraction G H g hg hf
  have hu' : P (ModuleCat.of R (⊤ : Submodule R (LinearMap.ker (awayMap G H g hg f)))) :=
    he ▸ hu
  exact P.prop_of_iso (LinearEquiv.ofTop (⊤ : Submodule R
    (LinearMap.ker (awayMap G H g hg f))) rfl).toModuleIso hu'

end Lech.Homogeneous


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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

namespace Lech.Homogeneous
open HomogeneousLocalization CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
attribute [local instance] awayAddCommGroup

lemma away_torsion (I : Ideal R) {f : A} {d : ℕ} (hf : f ∈ G d)
    (hT : powerTorsion I (ModuleCat.of R A)) :
    powerTorsion I (ModuleCat.of R (Away G f)) := by
  obtain ⟨a,ha⟩ := hT
  refine ⟨a,?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective G hf x
  let c : G (j*d) := ⟨b,by simpa only [nsmul_eq_mul,Nat.cast_id] using hb⟩
  change r • fraction G hf j c=0
  rw [←map_smul]
  have hc : r • c=0 := Subtype.ext (Module.mem_annihilator.mp (ha hr) b)
  rw [hc,map_zero]

variable (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A),g (r • a)=r • g a)
  {f : A} {d : ℕ} (hf : f ∈ G d) (I : Ideal R) (ell : TorsionLength I)
attribute [local irreducible] awayMap gradedMap kernelFraction
include hf in
lemma away_kernel_zero_torsion (hds : ell.DirectSumZero)
    (hT : powerTorsion I (ModuleCat.of R A))
    (hker : ∀ n,ell.value (ModuleCat.of R (gradedMap G H g hg n).ker)=0) :
    ell.value (ModuleCat.of R (awayMap G H g hg f).ker)=0 := by
  have htK : powerTorsion I (ModuleCat.of R (awayMap G H g hg f).ker) :=
    powerTorsion_submodule I _ (away_torsion G I hf hT)
  have hz : ell.zeroClass (ModuleCat.of R (awayMap G H g hg f).ker) := by
    apply kernel_property G H g hg hf ell.zeroClass
    · intro n
      exact ⟨powerTorsion_submodule I _ (powerTorsion_submodule I (G n) hT),hker n⟩
    · intro U hU
      refine ⟨powerTorsion_submodule I _ htK,?_⟩
      have hh := ell.iSup_zero_torsion hds (fun n : ULift.{u} ℕ => U n.down) htK
        (fun n => (hU n.down).2)
      have he : (⨆ n : ULift.{u} ℕ,U n.down) = ⨆ n : ℕ,U n := by
        simp only [iSup_ulift]
      rw [he] at hh
      exact hh
  exact hz.2
end Lech.Homogeneous

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

lemma chart_kernel_zero_torsion (hds : ell.DirectSumZero)
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ} (hf : f ∈ sourceGrade I h d) :
    ell.value (ModuleCat.of R (chartMapR I z hz f).ker)=0 := by
  unfold chartMapR
  apply Homogeneous.away_kernel_zero_torsion (R:=R) (A:=MvPolynomial (Fin h) (R ⧸ I))
    (B:=IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) hf I ell hds
    (torsion_of_quotient_scalar I (MvPolynomial (Fin h) (R ⧸ I)))
  exact mapR_degree_kernel_zero_torsion I z hz ell hh hmu ha

end Lech.SourceGraded

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalCoefficientSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

lemma coefficientComparison_kernel (s : Finset (Fin (n+1))) :
    (coefficientComparison I z hz hgen s).ker =
      (SourceGraded.chartMapR I z hgen (coefficientDenominator I s)).ker := by
  ext x
  change (coefficientTargetRename I z hz hgen s) _=0 ↔ _
  exact map_eq_zero_iff _ (coefficientTargetRename I z hz hgen s).injective

lemma coefficientComparison_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
    (s : Finset (Fin (n+1))) :
    ell.value (ModuleCat.of R (coefficientComparison I z hz hgen s).ker)=0 := by
  rw [coefficientComparison_kernel]
  exact SourceGraded.chart_kernel_zero_torsion I z hgen ell hds (Nat.succ_pos _) hmu ha
    (coefficientDenominator_mem I s)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalFibre
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory IdealGraded HomogeneousLocalization
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.coefRing
attribute [local instance] OAI.Lech.ReesRoot.exRing
attribute [local instance] OAI.Lech.ReesRoot.coefModule
attribute [local instance] OAI.Lech.ReesRoot.exModule
attribute [local instance] OAI.Lech.ReesRoot.coefficientPModule
attribute [local instance] OAI.Lech.ReesRoot.exceptionalPModule
lemma coefficientComparisonLinear_kernel_zero_oai (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
    (s : Finset (Fin (n+1))) :
    ell.value (ModuleCat.of R (coefficientComparisonLinear I z hz hgen s).ker)=0 := by
  change ell.value (ModuleCat.of R (coefficientComparison I z hz hgen s).ker)=0
  exact coefficientComparison_kernel_zero I z hz hgen ell hds hmu ha s

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.coefficientComparisonLinear_kernel_zero_oai.{u} := @OAI.Lech.ReesRoot.coefficientComparisonLinear_kernel_zero_oai.{u}
