-- Prove2me | solution 1 for OAI.PermanentBorder.SpectralDimension.spectral_effective_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:58:00.797985+00:00
-- url     : https://prove2.me/submissions/6b234b60-5621-42f5-bedd-d9c324971f59

import Mathlib
import Definitions.Def_OAIQWPB000
import Theorems.Thm_OAI_PermanentBorder_CurveFamily_half_curve_parameter_bound

section
-- module Solutions.OAIQW_PermanentBorder.Multigraded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

lemma project_mul {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (g : MvPolynomial σ K) (d : G) :
    weightedHomogeneousComponent w d (a * g) =
      a * weightedHomogeneousComponent w (d-e) g := by
  classical
  ext z
  simp only [coeff_weightedHomogeneousComponent, coeff_mul]
  have hi : (if Finsupp.weight w z = d then
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z, a.coeff xy.1 * g.coeff xy.2 else 0) =
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z,
        if Finsupp.weight w z = d then a.coeff xy.1 * g.coeff xy.2 else 0 := by
    rw [Finset.sum_ite_irrel]
    simp
  rw [hi]
  apply Finset.sum_congr rfl
  rintro ⟨x,y⟩ hxy
  have hsum : x+y=z := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
  by_cases hx : a.coeff x = 0
  · simp [hx]
  · have hwe : Finsupp.weight w x = e := ha hx
    have hcond : Finsupp.weight w z = d ↔ Finsupp.weight w y = d-e := by
      rw [← hsum, map_add, hwe]
      rw [eq_sub_iff_add_eq, add_comm]
    simp only [hcond]
    split_ifs <;> simp

end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SmoothSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma intWeight_homogeneous {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f.IsHomogeneous d := by
  intro s hs
  change Finsupp.weight (fun _ : σ => (1 : ℕ)) s = d
  rw [← Finsupp.degree_eq_weight_one]
  exact_mod_cast (intWeight_degree s ▸ hf hs)

end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConductorDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Conductor
open Module

section DualImage
variable {S B A : Type*} [CommRing S] [IsDomain S] [CommRing B] [CommRing A]
  [Algebra S B] [Algebra S A] [Algebra B A] [IsScalarTower S B A]
  [NoZeroSMulDivisors S A]
variable (hi : Function.Injective (algebraMap B A))
  (hden : ∀ x : A, ∃ s : S, s ≠ 0 ∧ ∃ b : B, s • x = algebraMap B A b)
  (lam : B →ₗ[S] S) (e : B ≃ₗ[S] Module.Dual S B)
  (he : ∀ a b : B, e a b = lam (a*b))

include hi hden e he

theorem in_dual_restriction_image_iff (a : B) :
    (∃ ℓ : A →ₗ[S] S, ∀ b : B, ℓ (algebraMap B A b) = lam (a*b)) ↔
      a ∈ algebraConductor B A := by
  constructor
  · rintro ⟨ℓ, hℓ⟩ x
    let ψ : B →ₗ[S] S :=
      { toFun := fun b => ℓ (algebraMap B A b * x)
        map_add' := by intro b c; simp [add_mul]
        map_smul' := by
          intro s b
          change ℓ ((IsScalarTower.toAlgHom S B A) (s • b) * x) = _
          rw [map_smul, smul_mul_assoc, map_smul]
          rfl }
    let c : B := e.symm ψ
    have hc (b : B) : e c b = ℓ (algebraMap B A b*x) := by
      change e (e.symm ψ) b = ψ b
      rw [e.apply_symm_apply]
    obtain ⟨s, hs, z, hz⟩ := hden x
    have hsc : s • c = a*z := by
      apply e.injective
      ext b
      calc
        e (s • c) b = s • (e c b) := by simp
        _ = s • ℓ (algebraMap B A b*x) := by rw [hc]
        _ = ℓ (algebraMap B A b * (s • x)) := by
          rw [mul_smul_comm, map_smul]
        _ = lam (a*(b*z)) := by rw [hz, ← map_mul, hℓ]
        _ = e (a*z) b := by rw [he]; congr 1; ring
    refine ⟨c, ?_⟩
    apply smul_right_injective A hs
    calc
      s • algebraMap B A c = (IsScalarTower.toAlgHom S B A) (s • c) := by rw [map_smul]; rfl
      _ = algebraMap B A (a*z) := by rw [hsc]; rfl
      _ = algebraMap B A a * (s • x) := by rw [map_mul, hz]
      _ = s • (algebraMap B A a * x) := mul_smul_comm _ _ _
  · intro ha
    refine ⟨lam.comp (conductorMultiplication hi a ha), ?_⟩
    intro b
    simp
end DualImage
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Module

section SmithDual
variable {S V W ι : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W]
  [Fintype ι]

theorem exists_dual_cokernel_equiv (b : Basis ι S W) (i : V →ₗ[S] W)
    (hi : Function.Injective i) (hrank : Module.finrank S V = Module.finrank S W) :
    Nonempty ((W ⧸ LinearMap.range i) ≃ₗ[S]
      ((Module.Dual S V) ⧸ LinearMap.range i.dualMap)) := by
  classical
  let j := LinearEquiv.ofInjective i hi
  have hrank' : Module.finrank S (LinearMap.range i) = Module.finrank S W := by
    rw [← j.finrank_eq, hrank]
  obtain ⟨bw, a, bn, hh⟩ := (LinearMap.range i).exists_smith_normal_form_of_rank_eq b hrank'
  let bv : Basis ι S V := bn.map j.symm
  have hib (k : ι) : i (bv k) = a k • bw k := by
    change i (j.symm (bn k)) = a k • bw k
    rw [← hh]
    exact congrArg Subtype.val (j.apply_symm_apply (bn k))
  let α : W ≃ₗ[S] Module.Dual S V := bw.equiv bv.dualBasis (Equiv.refl ι)
  let β : V ≃ₗ[S] Module.Dual S W := bv.equiv bw.dualBasis (Equiv.refl ι)
  have hid : α.toLinearMap.comp i = i.dualMap.comp β.toLinearMap := by
    apply bv.ext
    intro k
    apply bv.ext
    intro l
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.dualMap_apply]
    rw [hib, map_smul, show α (bw k) = bv.dualBasis k by simp [α],
      show β (bv k) = bw.dualBasis k by simp [β], hib]
    simp only [LinearMap.smul_apply, LinearMap.map_smul, Basis.dualBasis_apply]
    by_cases h : k = l
    · simp [h]
    · simp [h]
  have hr : Submodule.map α.toLinearMap (LinearMap.range i) = LinearMap.range i.dualMap := by
    rw [← LinearMap.range_comp, hid, LinearMap.range_comp]
    rw [β.range, Submodule.map_top]
  exact ⟨Submodule.Quotient.equiv _ _ α hr⟩

end SmithDual
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Module
section Colength
variable {S B A : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [CommRing B] [CommRing A] [Algebra S B] [Algebra S A] [Algebra B A]
  [IsScalarTower S B A] [NoZeroSMulDivisors S A] [Module.Finite S A]

omit [IsPrincipalIdealRing S] [NoZeroSMulDivisors S A] in

theorem finrank_eq_of_denominators
    (hi : Function.Injective (algebraMap B A))
    (hden : ∀ x : A, ∃ s : S, s ≠ 0 ∧ ∃ b : B, s • x = algebraMap B A b) :
    Module.finrank S B = Module.finrank S A := by
  let i : B →ₗ[S] A := (IsScalarTower.toAlgHom S B A).toLinearMap
  have ht : Module.IsTorsion S (A ⧸ LinearMap.range i) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨s, hs, b, hb⟩ := hden x
      refine ⟨⟨s, mem_nonZeroDivisors_iff_ne_zero.mpr hs⟩, ?_⟩
      change s • (Submodule.Quotient.mk x : A ⧸ LinearMap.range i) = 0
      rw [← Submodule.Quotient.mk_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, hb.symm⟩
  have hr := (LinearMap.range i).finrank_quotient_add_finrank
  rw [ht.finrank_eq_zero, zero_add] at hr
  exact (LinearEquiv.ofInjective i hi).finrank_eq.trans hr

end Colength
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Module

section RootEmbedding
variable {Q L : Type*} [Field Q] [Field L] [Algebra Q L]
variable {f : Q[X]} (hf : f.Monic)

include hf in

theorem rootEvaluation_injective (hsep : f.Separable)
    (hsplit : (f.map (algebraMap Q L)).Splits) :
    Function.Injective (rootEvaluation (f := f) (L := L)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  let p := AdjoinRoot.modByMonicHom hf z
  have hpz : AdjoinRoot.mk f p = z := AdjoinRoot.mk_leftInverse hf z
  have hpd : p.degree < f.degree := by
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    exact degree_modByMonic_lt g hf
  have hp : p = 0 := by
    by_contra hp
    have hpmap : p.map (algebraMap Q L) ≠ 0 := mt
      (fun h => Polynomial.map_injective _ (algebraMap Q L).injective (h.trans (Polynomial.map_zero _).symm)) hp
    have hc : Fintype.card (f.rootSet L) = f.natDegree := by
      exact card_rootSet_eq_natDegree hsep hsplit
    have hd : (p.map (algebraMap Q L)).natDegree < Fintype.card (f.rootSet L) := by
      rw [natDegree_map, hc]
      exact natDegree_lt_natDegree hp hpd
    apply hpmap
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (p.map (algebraMap Q L)) (f := fun x : f.rootSet L => x.val) Subtype.val_injective ?_ hd
    intro x
    have := congrFun hz x
    rw [← hpz, rootEvaluation_mk] at this
    simpa only [eval_map, aeval_def, Pi.zero_apply] using this
  rw [← hpz, hp, map_zero]
end RootEmbedding

section Normalization
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable {f : Q[X]} (hf : f.Monic) (hsep : f.Separable)

include hf hsep in

theorem finite_integralClosure_adjoinRoot :
    Module.Finite S (integralClosure S (AdjoinRoot f)) := by
  let L := f.SplittingField
  let : Algebra.IsSeparable Q L :=
    Algebra.isSeparable_of_separable_splitting_field Q L hsep
  let : Module.Finite S (integralClosure S L) :=
    IsIntegralClosure.finite S Q L (integralClosure S L)
  let ev (x : f.rootSet L) : AdjoinRoot f →ₐ[S] L :=
    (AdjoinRoot.liftAlgHom f (Algebra.ofId Q L) x.val
      (aeval_eq_zero_of_mem_rootSet x.property)).restrictScalars S
  let ι : integralClosure S (AdjoinRoot f) →ₗ[S] (f.rootSet L → integralClosure S L) :=
    { toFun := fun z x => ⟨ev x z.val, IsIntegral.map (ev x) z.property⟩
      map_add' := by intro z w; ext x; simp
      map_smul' := by intro s z; ext x; simp }
  apply Module.Finite.of_injective ι
  intro z w h
  apply Subtype.ext
  apply rootEvaluation_injective hf hsep (SplittingField.splits f)
  funext x
  exact congrArg Subtype.val (congrFun h x)
end Normalization
end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Conductor
open Polynomial Module
section GenericLattice
variable {S Q : Type*} [CommRing S] [IsDomain S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable (f : S[X])

omit [IsDomain S] in

theorem genericBaseChange_injective (hf : f.Monic) :
    Function.Injective (genericBaseChange (Q := Q) f) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [genericBaseChange_mk, AdjoinRoot.mk_eq_zero] at hz
  rw [AdjoinRoot.mk_eq_zero, ← modByMonic_eq_zero_iff_dvd hf]
  apply Polynomial.map_injective (algebraMap S Q) (IsFractionRing.injective S Q)
  rw [Polynomial.map_zero, map_modByMonic _ hf,
    (modByMonic_eq_zero_iff_dvd (hf.map _)).mpr hz]

theorem genericBaseChange_denominators
    (x : AdjoinRoot (f.map (algebraMap S Q))) :
    ∃ s : S, s ≠ 0 ∧ ∃ b : AdjoinRoot f,
      s • x = genericBaseChange (Q := Q) f b := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨s, hs, hp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors S) p
  refine ⟨s, mem_nonZeroDivisors_iff_ne_zero.mp hs,
    AdjoinRoot.mk f (IsLocalization.integerNormalization (nonZeroDivisors S) p), ?_⟩
  rw [genericBaseChange_mk, hp]
  exact (map_smul (((AdjoinRoot.mkₐ (f.map (algebraMap S Q))).restrictScalars S).toLinearMap) s p).symm

variable (hf : f.Monic)

omit [IsDomain S] in
theorem normalizationInclusion_injective :
    Function.Injective (normalizationInclusion (Q := Q) f hf) := by
  intro z w h
  apply genericBaseChange_injective (Q := Q) f hf
  exact congrArg Subtype.val h

theorem normalizationInclusion_denominators
    (x : integralClosure S (AdjoinRoot (f.map (algebraMap S Q)))) :
    ∃ s : S, s ≠ 0 ∧ ∃ b : AdjoinRoot f,
      s • x = normalizationInclusion (Q := Q) f hf b := by
  obtain ⟨s, hs, b, hb⟩ := genericBaseChange_denominators f x.val
  exact ⟨s, hs, b, Subtype.ext hb⟩
end GenericLattice
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Module
section ActualNormalization
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable {f : S[X]} (hf : f.Monic)
local notation "R" => integralClosure S (AdjoinRoot (f.map (algebraMap S Q)))

omit [IsDomain S] [IsPrincipalIdealRing S] in

theorem normalization_torsionFree : NoZeroSMulDivisors S R := by
  let ι : R →ₗ[S] AdjoinRoot (f.map (algebraMap S Q)) :=
    (integralClosure S (AdjoinRoot (f.map (algebraMap S Q)))).val.toLinearMap
  have : NoZeroSMulDivisors S (AdjoinRoot (f.map (algebraMap S Q))) := by
    constructor
    intro s x h
    rw [← IsScalarTower.algebraMap_smul Q s x] at h
    rcases eq_zero_or_eq_zero_of_smul_eq_zero h with hs | hx
    · exact Or.inl ((IsFractionRing.injective S Q) (hs.trans (map_zero _).symm))
    · exact Or.inr hx
  exact Function.Injective.noZeroSMulDivisors ι Subtype.val_injective
    (map_zero ι) (map_smul ι)

end ActualNormalization
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
section Semilocal
variable {S A : Type*} [CommRing S] [IsLocalRing S]
  [CommRing A] [Algebra S A] [Module.Finite S A]

include S in

theorem finite_maximalSpectrum_of_finite_local : Finite (MaximalSpectrum A) := by
  classical
  let m := IsLocalRing.maximalIdeal S
  let J := m.map (algebraMap S A)
  have hle (M : MaximalSpectrum A) : J ≤ M.asIdeal := by
    change m.map (algebraMap S A) ≤ M.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    have hm : (M.asIdeal.comap (algebraMap S A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M.asIdeal
    exact (IsLocalRing.eq_maximalIdeal hm).symm.le
  let : Algebra (S ⧸ m) (A ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map)
  have : IsScalarTower S (S ⧸ m) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  have : Module.Finite (S ⧸ m) (A ⧸ J) :=
    Module.Finite.of_restrictScalars_finite S _ _
  let : Field (S ⧸ m) := Ideal.Quotient.field m
  have : IsArtinianRing (A ⧸ J) := IsArtinianRing.of_finite (S ⧸ m) _
  have hker : RingHom.ker (Ideal.Quotient.mk J) = J := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  let ι : MaximalSpectrum A → MaximalSpectrum (A ⧸ J) := fun M =>
    ⟨M.asIdeal.map (Ideal.Quotient.mk J),
      Ideal.IsMaximal.map_of_surjective_of_ker_le (Ideal.Quotient.mk_surjective)
        (by rw [hker]; exact hle M)⟩
  apply Finite.of_injective ι
  intro M N h
  apply MaximalSpectrum.ext
  have he := congrArg MaximalSpectrum.asIdeal h
  have hi (P : MaximalSpectrum A) :
      (P.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ (Ideal.Quotient.mk_surjective)]
    rw [← RingHom.ker_eq_comap_bot, hker, sup_of_le_left (hle P)]
  exact (hi M).symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk J)) he).trans (hi N))
end Semilocal

section FieldNormalization
variable {S Q L : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [FiniteDimensional Q L] [Algebra.IsSeparable Q L]

include Q in

theorem integralClosure_isPrincipalIdealRing :
    IsPrincipalIdealRing (integralClosure S L) := by
  have : Module.Finite S (integralClosure S L) :=
    IsIntegralClosure.finite S Q L (integralClosure S L)
  have : Finite (MaximalSpectrum (integralClosure S L)) :=
    finite_maximalSpectrum_of_finite_local (S := S)
  have : IsDedekindDomain (integralClosure S L) :=
    integralClosure.isDedekindDomain S Q L
  apply IsPrincipalIdealRing.of_finite_maximals
  rw [← MaximalSpectrum.range_asIdeal]
  exact Set.finite_range _
end FieldNormalization
end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConductorLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Conductor
open Module Polynomial
section CokernelEquiv
variable {S B A : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [CommRing B] [CommRing A] [Algebra S B] [Algebra S A] [Algebra B A]
  [IsScalarTower S B A] [NoZeroSMulDivisors S A] [Module.Finite S A]

theorem exists_conductor_cokernel_equiv
    (hi : Function.Injective (algebraMap B A))
    (hden : ∀ x : A, ∃ s : S, s ≠ 0 ∧ ∃ b : B, s • x = algebraMap B A b)
    (lam : B →ₗ[S] S) (e : B ≃ₗ[S] Module.Dual S B)
    (he : ∀ a b : B, e a b = lam (a*b)) :
    Nonempty ((B ⧸ (algebraConductor B A).restrictScalars S) ≃ₗ[S]
      (A ⧸ LinearMap.range (IsScalarTower.toAlgHom S B A).toLinearMap)) := by
  classical
  let i : B →ₗ[S] A := (IsScalarTower.toAlgHom S B A).toLinearMap
  have hr : Submodule.map e.toLinearMap ((algebraConductor B A).restrictScalars S) =
      LinearMap.range i.dualMap := by
    ext ℓ
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨L, hL⟩ := (in_dual_restriction_image_iff hi hden lam e he a).mpr ha
      refine ⟨L, ?_⟩
      ext b
      exact (hL b).trans (he a b).symm
    · rintro ⟨L, rfl⟩
      refine ⟨e.symm (i.dualMap L), ?_, by simp⟩
      apply (in_dual_restriction_image_iff hi hden lam e he _).mp
      refine ⟨L, ?_⟩
      intro b
      rw [← he, e.apply_symm_apply]
      rfl
  let eqv := Submodule.Quotient.equiv _ _ e hr
  obtain ⟨d⟩ := exists_dual_cokernel_equiv (Module.Free.chooseBasis S A) i hi
    (finrank_eq_of_denominators hi hden)
  exact ⟨eqv.trans d.symm⟩
end CokernelEquiv

section NormalizationCokernel
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable {f : S[X]} (hf : f.Monic)
local notation "R" => integralClosure S (AdjoinRoot (f.map (algebraMap S Q)))

theorem exists_normalization_conductor_cokernel_equiv
    (hsep : (f.map (algebraMap S Q)).Separable) :
    letI := (normalizationInclusion (Q := Q) f hf).toRingHom.toAlgebra
    Nonempty ((AdjoinRoot f ⧸ (algebraConductor (AdjoinRoot f) R).restrictScalars S) ≃ₗ[S]
      (R ⧸ LinearMap.range (normalizationInclusion (Q := Q) f hf).toLinearMap)) := by
  let := (normalizationInclusion (Q := Q) f hf).toRingHom.toAlgebra
  have : Module.Finite S R := finite_integralClosure_adjoinRoot (hf.map _) hsep
  have : NoZeroSMulDivisors S R := normalization_torsionFree (f := f)
  exact exists_conductor_cokernel_equiv
    (normalizationInclusion_injective (Q := Q) f hf)
    (normalizationInclusion_denominators (Q := Q) f hf)
    (topRemainderCoefficient hf) (coefficientPairingEquiv hf) (coefficientPairingEquiv_apply hf)
end NormalizationCokernel
end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PencilSeparability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PencilSeparability
open Polynomial Matrix
section Specialization
variable {R K L : Type*} [CommRing R] [Field K] [Field L]

theorem monic_generic_separable (f : R[X]) (hf : f.Monic)
    (σ : R →+* K) (φ : R →+* L) (hφ : Function.Injective φ)
    (hs : (f.map σ).Separable) : (f.map φ).Separable := by
  let g := f.derivative
  have hσd : (f.map σ).natDegree = f.natDegree := hf.natDegree_map σ
  have hφd : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  have hd : (g.map σ).natDegree ≤ g.natDegree := natDegree_map_le
  have hσ : σ (resultant f g) ≠ 0 := by
    rw [← resultant_map_map f g f.natDegree g.natDegree, ← hσd]
    conv_lhs => rw [show g.natDegree = (g.map σ).natDegree +
      (g.natDegree - (g.map σ).natDegree) by omega]
    rw [resultant_add_right_deg _ _ _ _ _ le_rfl]
    have hc : (f.map σ).coeff (f.map σ).natDegree = 1 := (hf.map σ).coeff_natDegree
    rw [hc, one_pow, one_mul]
    exact resultant_ne_zero _ _ (by simpa only [Separable, g, derivative_map] using hs)
  have hres : resultant f g ≠ 0 := fun h => hσ (h ▸ σ.map_zero)
  have hφg : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hφ g
  apply (isUnit_resultant_iff_isCoprime (hf.map φ)).mp
  apply isUnit_iff_ne_zero.mpr
  rw [derivative_map, hφd, hφg, resultant_map_map]
  exact fun h => hres (hφ (h.trans φ.map_zero.symm))

end Specialization
section Scaling
variable {K : Type*} [Field K]

theorem separable_comp_linear (f : K[X]) (hf : f.Separable) (a : K) (ha : a ≠ 0) :
    (f.comp (C a * X)).Separable := by
  obtain ⟨u,v,h⟩ := hf
  let p : K[X] := C a * X
  refine ⟨u.comp p, C a⁻¹ * v.comp p, ?_⟩
  have hc := congrArg (fun z : K[X] => z.comp p) h
  simp only [add_comp, mul_comp, one_comp] at hc
  have hd : derivative p = C a := by
    simp only [p, derivative_mul, derivative_C, zero_mul, derivative_X, mul_one, zero_add]
  change u.comp p * f.comp p + (C a⁻¹ * v.comp p) * derivative (f.comp p) = 1
  rw [derivative_comp, hd]
  have haC : C a⁻¹ * C a = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ ha, C_1]
  calc
    _ = u.comp p * f.comp p + (C a⁻¹ * C a) *
        (v.comp p * f.derivative.comp p) := by ring
    _ = 1 := by rw [haC, one_mul]; exact hc

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem charpoly_smul_eq_comp (A : Matrix ι ι K) (a : K) (ha : a ≠ 0) :
    (a • A).charpoly = C (a ^ Fintype.card ι) * A.charpoly.comp (C a⁻¹ * X) := by
  let φ : K[X] →+* K[X] := eval₂RingHom C (C a⁻¹ * X)
  have hm : (a • A).charmatrix = C a • A.charmatrix.map φ := by
    apply Matrix.ext
    intro i j
    by_cases h : i = j
    · subst j
      simp only [charmatrix_apply, diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul,
        Matrix.map_apply, φ, coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_C, map_mul]
      have hx : C a * C a⁻¹ = (1 : K[X]) := by
        rw [← C_mul, mul_inv_cancel₀ ha, C_1]
      rw [mul_sub, ← mul_assoc, hx, one_mul]
    · simp only [charmatrix_apply, diagonal_apply_ne _ h, Matrix.smul_apply, smul_eq_mul,
        Matrix.map_apply, zero_sub, φ, coe_eval₂RingHom, eval₂_neg,
        eval₂_C, map_mul, mul_neg]
  rw [Matrix.charpoly, hm, Matrix.det_smul]
  have hd : (A.charmatrix.map φ).det = φ A.charpoly := (φ.map_det _).symm
  rw [hd]
  simp only [map_pow, φ, coe_eval₂RingHom, Polynomial.comp]

theorem separable_charpoly_smul (A : Matrix ι ι K) (hA : A.charpoly.Separable)
    (a : K) (ha : a ≠ 0) : (a • A).charpoly.Separable := by
  rw [charpoly_smul_eq_comp A a ha]
  exact (separable_comp_linear A.charpoly hA a⁻¹ (inv_ne_zero ha)).unit_mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha)))
end Scaling

section Pencil
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem distinct_slope_pencil_separable (θ : ι → K) (hθ : Function.Injective θ)
    (A : Matrix ι ι K) :
    ((-((X : K[X]) • (Matrix.diagonal θ).map C + A.map C)).charpoly.map
      (algebraMap K[X] (FractionRing K[X]))).Separable := by
  let Q := FractionRing K[X]
  let t : Q := algebraMap K[X] Q X
  have ht : Transcendental K t :=
    (transcendental_algebraMap_iff (IsFractionRing.injective K[X] Q)).mpr
      (transcendental_X K)
  have hti : Transcendental K t⁻¹ := by
    simpa only [Transcendental, IsAlgebraic.inv_iff] using ht
  let φ : K[X] →+* Q := (aeval t⁻¹).toRingHom
  have hφ : Function.Injective φ := transcendental_iff_injective.mp hti
  let B : Matrix ι ι K[X] := -((Matrix.diagonal θ).map C + (X : K[X]) • A.map C)
  have hB : (B.charpoly.map (evalRingHom (0 : K))).Separable := by
    rw [← charpoly_map]
    have he : B.map (evalRingHom (0 : K)) = Matrix.diagonal (fun i => -θ i) := by
      apply Matrix.ext
      intro i j
      by_cases h : i = j <;> simp [B, h]
    rw [he, charpoly_diagonal, separable_prod_X_sub_C_iff]
    exact fun i j hij => hθ (neg_injective hij)
  have hs := monic_generic_separable B.charpoly B.charpoly_monic
    (evalRingHom (0 : K)) φ hφ hB
  rw [← charpoly_map] at hs
  have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  have hm : (-((X : K[X]) • (Matrix.diagonal θ).map C + A.map C)).map
      (algebraMap K[X] Q) = t • B.map φ := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, map_neg, map_add, map_mul, B]
    have hc (x : K) : algebraMap K[X] Q (C x) = algebraMap K Q x :=
      (IsScalarTower.algebraMap_apply K K[X] Q x).symm
    simp only [φ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, aeval_X, hc]
    change -(t * algebraMap K Q ((Matrix.diagonal θ) i j) + algebraMap K Q (A i j)) =
      t * -(algebraMap K Q ((Matrix.diagonal θ) i j) + t⁻¹ * algebraMap K Q (A i j))
    rw [mul_neg, mul_add, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
  rw [← charpoly_map, hm]
  exact separable_charpoly_smul (B.map φ) hs t ht0
end Pencil
end PermanentBorder.PencilSeparability

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.QuotientFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Bivariate
open Polynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem inField_iff_lifts (F : IntermediateField K L) (P : L[X][X]) :
    InField F P ↔ ∃ Q : F[X][X], map F.val.toRingHom Q = P := by
  change (∀ a b, (P.coeff a).coeff b ∈ F) ↔
    ∃ Q : F[X][X], Polynomial.map (Polynomial.mapRingHom F.val.toRingHom) Q = P
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h a
    have hp : P.coeff a ∈ Polynomial.lifts F.val.toRingHom := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro b
      exact ⟨⟨_,h a b⟩,rfl⟩
    exact (Polynomial.mem_lifts _).mp hp
  · intro h a b
    obtain ⟨Q,hQ⟩ := h a
    rw [← hQ]
    change (Polynomial.map F.val.toRingHom Q).coeff b ∈ F
    rw [Polynomial.coeff_map]
    exact (Q.coeff b).property

end PermanentBorder.Bivariate

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Monogenic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.NormalizationMonogenic
open Polynomial

section Nilpotent
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

lemma adjoin_eq_top_of_nilpotent_reduction (u : A) (p : R[X])
    (hp : IsNilpotent (aeval u p))
    (h : ∀ z : A, ∃ q : R[X], ∃ w : A, z = aeval u q + aeval u p * w) :
    Algebra.adjoin R {u} = ⊤ := by
  have hd (n : ℕ) (z : A) :
      ∃ q : R[X], ∃ w : A, z = aeval u q + (aeval u p)^n*w := by
    induction n with
    | zero => exact ⟨0,z,by simp⟩
    | succ n ih =>
      obtain ⟨q,w,hw⟩ := ih
      obtain ⟨r,v,hv⟩ := h w
      refine ⟨q+p^n*r,v,?_⟩
      rw [hw,hv]
      simp only [map_add,map_mul,map_pow,pow_succ]
      ring
  rcases hp with ⟨n,hn⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
  intro z
  obtain ⟨q,w,hw⟩ := hd n z
  exact ⟨q,by simpa [hn] using hw.symm⟩

end Nilpotent

section Nakayama
variable {A : Type*} [CommRing A] [IsNoetherianRing A]

lemma nilradical_eq_span_of_mod_square
    (ρ v a : A) (hρ : Ideal.span {ρ} = nilradical A)
    (ha : a ∈ nilradical A) (hr : ρ - v*a ∈ (nilradical A)^2) :
    nilradical A = Ideal.span {a} := by
  apply le_antisymm
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian (nilradical A)) Ideal.radical_le_jacobson
    nth_rw 1 [← hρ]
    rw [Ideal.span_le]
    intro z hz
    have heq : z = ρ := Set.mem_singleton_iff.mp hz
    subst z
    change ρ ∈ Ideal.span {a} ⊔ nilradical A • nilradical A
    have hr' : ρ - v*a ∈ Ideal.span {a} ⊔ nilradical A • nilradical A := by
      apply Submodule.mem_sup_right
      simpa only [Ideal.smul_eq_mul, pow_two] using hr
    have hvp : v*a ∈ Ideal.span {a} ⊔ nilradical A • nilradical A :=
      Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    simpa using (Ideal.span {a} ⊔ nilradical A • nilradical A).add_mem hr' hvp
  · exact Ideal.span_le.mpr (by simpa using ha)

end Nakayama

section Global
variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A]
  [Algebra K A] [Module.Finite K A] [IsPrincipalIdealRing A]

lemma exists_adjoin_eq_top : ∃ u : A, Algebra.adjoin K {u} = ⊤ := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsNoetherianRing A := IsNoetherianRing.of_finite K A
  let J := nilradical A
  let ρ := Submodule.IsPrincipal.generator J
  have hJρ : Ideal.span {ρ} = J := Submodule.IsPrincipal.span_singleton_generator J
  have hρ : ρ ∈ J := by rw [← hJρ]; exact Ideal.subset_span (by simp)
  let ι := MaximalSpectrum A
  let : Fintype ι := Fintype.ofFinite _
  let θ : ι → K := fun i => Infinite.natEmbedding K ((Fintype.equivFin ι) i).val
  have hθ : Function.Injective θ := (Infinite.natEmbedding K).injective.comp
    (Fin.val_injective.comp (Fintype.equivFin ι).injective)
  have hcop : Pairwise (fun i j : ι => IsCoprime (i.asIdeal ^ 2) (j.asIdeal ^ 2)) :=
    fun i j hij => (i.isCoprime_of_ne hij).pow
  obtain ⟨u,hu⟩ := Ideal.pi_quotient_surjective hcop
    (fun i => Ideal.Quotient.mk (i.asIdeal ^ 2) (algebraMap K A (θ i) + ρ))
  let p : K[X] := ∏ i : ι, (X - C (θ i))
  have hp0 (i : ι) : p.eval (θ i) = 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hp' (i : ι) : p.derivative.eval (θ i) ≠ 0 := by
    simpa only [eval₂_id] using
      (separable_prod_X_sub_C_iff.mpr hθ).eval₂_derivative_ne_zero
        (RingHom.id K) (by simpa only [eval₂_id] using hp0 i)
  have hρi (i : ι) : ρ ∈ i.asIdeal := by
    exact nilradical_le_prime i.asIdeal hρ
  have hut (i : ι) : Ideal.Quotient.mk i.asIdeal u =
      algebraMap K (A ⧸ i.asIdeal) (θ i) := by
    have h := congrArg (Ideal.Quotient.factor (Ideal.pow_le_self (by decide : 2 ≠ 0))) (hu i)
    change Ideal.Quotient.mk i.asIdeal u = Ideal.Quotient.mk i.asIdeal
      (algebraMap K A (θ i) + ρ) at h
    simpa [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (hρi i)] using h
  have hpu (i : ι) : Ideal.Quotient.mk (i.asIdeal ^ 2) (aeval u p) =
      algebraMap K (A ⧸ i.asIdeal ^ 2) (p.derivative.eval (θ i)) *
        Ideal.Quotient.mk (i.asIdeal ^ 2) ρ := by
    have hn : (Ideal.Quotient.mk (i.asIdeal ^ 2) ρ)^2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (hρi i) 2
    change (Ideal.Quotient.mkₐ K (i.asIdeal ^ 2)) (aeval u p) = _
    rw [← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hu i, map_add]
    change aeval (algebraMap K _ (θ i) + Ideal.Quotient.mk (i.asIdeal^2) ρ) p = _
    rw [aeval_add_of_sq_eq_zero _ _ _ hn]
    simp only [aeval_algebraMap_apply_eq_algebraMap_eval, hp0, map_zero, zero_add]
  obtain ⟨v,hv⟩ := Ideal.pi_quotient_surjective hcop
    (fun i => algebraMap K (A ⧸ i.asIdeal^2) ((p.derivative.eval (θ i))⁻¹))
  have hr : ρ - v * aeval u p ∈ J^2 := by
    rw [show J^2 = ⨅ i : ι, i.asIdeal^2 from IsArtinianRing.nilradical_pow_eq_iInf A 2]
    simp only [Ideal.mem_iInf]
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv i, hpu,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ (hp' i), map_one, one_mul, sub_self]
  have hpJ : aeval u p ∈ J := by
    rw [show J = ⨅ i : ι, i.asIdeal from IsArtinianRing.nilradical_eq_iInf A]
    simp only [Ideal.mem_iInf]
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change (Ideal.Quotient.mkₐ K i.asIdeal) (aeval u p) = 0
    rw [← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hut,
      aeval_algebraMap_apply_eq_algebraMap_eval, hp0, map_zero]
  have hJp : J = Ideal.span {aeval u p} :=
    nilradical_eq_span_of_mod_square ρ v (aeval u p) hJρ hpJ hr
  refine ⟨u, adjoin_eq_top_of_nilpotent_reduction u p ?_ ?_⟩
  · exact mem_nilradical.mp hpJ
  · intro z
    let (i : ι) : Field (A ⧸ i.asIdeal) := Ideal.Quotient.field _
    choose c hc using fun i : ι =>
      (IsAlgClosed.algebraMap_bijective_of_isIntegral
        (k := K) (K := A ⧸ i.asIdeal)).2 (Ideal.Quotient.mk i.asIdeal z)
    let q := Lagrange.interpolate Finset.univ θ c
    have hq (i : ι) : q.eval (θ i) = c i :=
      Lagrange.eval_interpolate_at_node _ hθ.injOn (Finset.mem_univ i)
    have hz : z - aeval u q ∈ J := by
      rw [show J = ⨅ i : ι, i.asIdeal from IsArtinianRing.nilradical_eq_iInf A]
      simp only [Ideal.mem_iInf]
      intro i
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      change _ = (Ideal.Quotient.mkₐ K i.asIdeal) (aeval u q)
      rw [← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hut,
        aeval_algebraMap_apply_eq_algebraMap_eval, hq, hc]
    rw [hJp,Ideal.mem_span_singleton] at hz
    obtain ⟨w,hw⟩ := hz
    exact ⟨q,w,by linear_combination hw⟩

end Global
end PermanentBorder.NormalizationMonogenic

namespace PermanentBorder.NormalizationMonogenic
open Polynomial
section LocalLift
variable {S B : Type*} [CommRing S] [IsLocalRing S] [CommRing B]
  [Algebra S B] [Module.Finite S B]

lemma adjoin_eq_top_of_residue_surjective (u : B)
    (hu : Function.Surjective fun p : S[X] =>
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S).map (algebraMap S B)) (aeval u p)) :
    Algebra.adjoin S {u} = ⊤ := by
  let A := Algebra.adjoin S {u}
  have him : (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S).map (algebraMap S B))) ''
      (A : Set B) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨p,hp⟩ := hu z
    refine ⟨aeval u p, ?_, hp⟩
    change aeval u p ∈ Algebra.adjoin S {u}
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p,rfl⟩
  have hspan := (IsLocalRing.quotient_span_eq_top_iff_span_eq_top (S := B) (A : Set B)).mp
    (by rw [him]; exact Submodule.span_univ)
  apply Subalgebra.toSubmodule_injective
  change A.toSubmodule = ⊤
  change Submodule.span S (A.toSubmodule : Set B) = ⊤ at hspan
  simpa only [Submodule.span_eq] using hspan

lemma exists_adjoin_eq_top_of_residue_principal
    [IsAlgClosed (IsLocalRing.ResidueField S)]
    [IsPrincipalIdealRing (B ⧸ (IsLocalRing.maximalIdeal S).map (algebraMap S B))] :
    ∃ u : B, Algebra.adjoin S {u} = ⊤ := by
  let J := (IsLocalRing.maximalIdeal S).map (algebraMap S B)
  let Q := B ⧸ J
  let K := IsLocalRing.ResidueField S
  let : Algebra K Q := Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map)
  have : IsScalarTower S K Q := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : Module.Finite K Q := Module.Finite.of_restrictScalars_finite S K Q
  obtain ⟨v,hv⟩ := exists_adjoin_eq_top (K := K) (A := Q)
  obtain ⟨u,hu⟩ := Ideal.Quotient.mk_surjective v
  refine ⟨u, adjoin_eq_top_of_residue_surjective u ?_⟩
  intro z
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hv
  obtain ⟨p,hp⟩ := hv z
  obtain ⟨p',hp'⟩ := Polynomial.map_surjective (IsLocalRing.residue S)
    Ideal.Quotient.mk_surjective p
  refine ⟨p', ?_⟩
  change (Ideal.Quotient.mkₐ S J) (aeval u p') = z
  rw [← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hu]
  rw [← hp, ← hp']
  exact (aeval_map_algebraMap K v p').symm

lemma exists_adjoin_eq_top_of_principal [IsPrincipalIdealRing B]
    [IsAlgClosed (IsLocalRing.ResidueField S)] :
    ∃ u : B, Algebra.adjoin S {u} = ⊤ := by
  have : IsPrincipalIdealRing (B ⧸ (IsLocalRing.maximalIdeal S).map (algebraMap S B)) :=
    IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  exact exists_adjoin_eq_top_of_residue_principal
end LocalLift
end PermanentBorder.NormalizationMonogenic

namespace PermanentBorder.NormalizationDerivation
open Polynomial TensorProduct

section Monogenic
variable {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

lemma scaledExtension_aeval (d : Derivation R S S) (u : B) (p q : S[X])
    (hu : Algebra.adjoin S {u} = ⊤)
    (hp : ∀ q : S[X], aeval u q = 0 ↔ p ∣ q) :
    scaledExtension d u p hu hp (aeval u q) = aeval u (hamiltonian d p q) :=
  by
    unfold scaledExtension
    apply Derivation.liftOfSurjective_apply

@[simp] lemma scaledExtension_algebraMap (d : Derivation R S S) (u : B) (p : S[X])
    (hu : Algebra.adjoin S {u} = ⊤)
    (hp : ∀ q : S[X], aeval u q = 0 ↔ p ∣ q) (s : S) :
    scaledExtension d u p hu hp (algebraMap S B s) =
      aeval u p.derivative * algebraMap S B (d s) := by
  rw [← aeval_C u s, scaledExtension_aeval, hamiltonian_C, map_mul, aeval_C]

@[simp] lemma scaledExtension_generator (d : Derivation R S S) (u : B) (p : S[X])
    (hu : Algebra.adjoin S {u} = ⊤)
    (hp : ∀ q : S[X], aeval u q = 0 ↔ p ∣ q) :
    scaledExtension d u p hu hp u = -aeval u (coeffDeriv d p) := by
  simpa only [aeval_X, hamiltonian_X, map_neg] using
    scaledExtension_aeval d u p X hu hp

end Monogenic
end PermanentBorder.NormalizationDerivation

namespace PermanentBorder.NormalizationDerivation
open Polynomial
section FractionGenerator
variable {S Q L B : Type*} [CommRing S] [IsDomain S] [Field Q] [Field L] [CommRing B]
  [Algebra S Q] [IsFractionRing S Q] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [Algebra S B] [Algebra B L] [IsScalarTower S B L] [IsIntegralClosure B S L]
  [Algebra.IsAlgebraic Q L]

lemma adjoin_fraction_generator {u : B} (hu : Algebra.adjoin S {u} = ⊤) :
    Algebra.adjoin Q {algebraMap B L u} = ⊤ := by
  have := IsIntegralClosure.isLocalization S Q L B
  let A := Algebra.adjoin Q {algebraMap B L u}
  have hb (b : B) : algebraMap B L b ∈ A := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hu
    obtain ⟨p,rfl⟩ := hu b
    change (IsScalarTower.toAlgHom S B L) (aeval u p) ∈ A
    rw [← aeval_algHom_apply]
    rw [← aeval_map_algebraMap Q]
    change aeval (algebraMap B L u) _ ∈ Algebra.adjoin Q {algebraMap B L u}
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨_,rfl⟩
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨⟨b,a⟩,he⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors S)) z
  obtain ⟨s,hs,ha⟩ := a.property
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have he' : z * algebraMap S L s = algebraMap B L b := by
    rw [IsScalarTower.algebraMap_apply S B L, ha]
    exact he
  have hq0 : algebraMap S Q s ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective S Q).ne hs0
  have hz : z = algebraMap Q L ((algebraMap S Q s)⁻¹) * algebraMap B L b := by
    rw [← he', IsScalarTower.algebraMap_apply S Q L]
    rw [mul_comm z, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq0, map_one, one_mul]
  rw [hz]
  exact A.mul_mem (A.algebraMap_mem _) (hb b)
end FractionGenerator

section Normalization
variable {R S Q L B : Type*} [CommRing R] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed S] [IsLocalRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [FiniteDimensional Q L] [Algebra.IsSeparable Q L]
  [CommRing B] [IsDedekindDomain B] [IsPrincipalIdealRing B]
  [Algebra S B] [Module.Finite S B] [Algebra B L] [IsScalarTower S B L]
  [IsIntegralClosure B S L] [Module.IsTorsionFree S B]
  [Algebra R S] [Algebra R B] [IsScalarTower R S B]

include Q L in

lemma exists_scaled_normalization_derivation (d : Derivation R S S) :
    ∃ (g : B) (D : Derivation R B B),
      differentIdeal S B = Ideal.span {g} ∧
      ∀ s : S, D (algebraMap S B s) = g * algebraMap S B (d s) := by
  obtain ⟨u,hu⟩ := NormalizationMonogenic.exists_adjoin_eq_top_of_principal (S := S) (B := B)
  have hi : IsIntegral S u := IsIntegralClosure.isIntegral S L u
  let p := minpoly S u
  have hp (q : S[X]) : aeval u q = 0 ↔ p ∣ q := minpoly.isIntegrallyClosed_dvd_iff hi q
  refine ⟨aeval u p.derivative, scaledExtension d u p hu hp, ?_, ?_⟩
  · have h := conductor_mul_differentIdeal S Q L u (adjoin_fraction_generator (Q := Q) hu)
    rw [conductor_eq_top_of_adjoin_eq_top hu, Ideal.top_mul] at h
    exact h
  · exact scaledExtension_algebraMap d u p hu hp
end Normalization
end PermanentBorder.NormalizationDerivation

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.LocalDerivations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.FrobeniusDVR
open IsDiscreteValuationRing
variable {K B : Type*} [CommRing K] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra K B]
local notation "v" => addVal B

lemma valuation_le_derivation_add_one (D : Derivation K B B) (z : B) :
    v z ≤ v (D z) + 1 := by
  obtain ⟨π,hπ⟩ := exists_irreducible B
  by_cases hz : z = 0
  · simp [hz, map_zero]
  obtain ⟨n,hn⟩ := associated_pow_irreducible hz hπ
  obtain ⟨u,hu⟩ := hn.symm
  rw [← hu]
  cases n with
  | zero => simp [pow_zero, addVal_eq_zero_of_unit]
  | succ n =>
    have hdiv : π^(n+1) ∣ π * D (π^(n+1) * ↑u) := by
      rw [Derivation.leibniz, Derivation.leibniz_pow]
      simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
      refine ⟨(n+1 : B) * D π * ↑u + π * D ↑u, ?_⟩
      rw [pow_succ]
      push_cast
      ring
    have hv := (addVal_le_iff_dvd (R := B)).mpr hdiv
    rw [hπ.addVal_pow, addVal_mul, addVal_uniformizer hπ] at hv
    simpa only [addVal_mul, hπ.addVal_pow, addVal_eq_zero_of_unit, add_zero,
      add_comm (1 : ℕ∞)] using hv

variable [CharP B 2]

omit [IsDomain B] [IsDiscreteValuationRing B] in
lemma derivation_square (D : Derivation K B B) (a : B) : D (a^2) = 0 := by
  have htwo : (2 : B) = 0 := CharP.cast_eq_zero _ 2
  simp [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, htwo]

omit [IsDomain B] [IsDiscreteValuationRing B] in
lemma derivation_square_plus (D : Derivation K B B) (x c d : B) :
    D (c^2+x*d^2) = D x * d^2 := by
  rw [map_add, derivation_square, Derivation.leibniz, derivation_square]
  simp only [smul_eq_mul, mul_zero, zero_add]
  exact mul_comm _ _

lemma valuation_square_plus_le (D : Derivation K B B) (x c d : B) :
    v (c^2+x*d^2) ≤ v (D x) + 2*v d + 1 := by
  have h := valuation_le_derivation_add_one D (c^2+x*d^2)
  simpa only [derivation_square_plus, addVal_mul, addVal_pow,
    nsmul_eq_mul, Nat.cast_ofNat] using h

omit [IsDomain B] [IsDiscreteValuationRing B] in
lemma branch_chain (D : Derivation K B B) (x y a b c d : B)
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    (b^2+y*d^2) * D x + (c^2+x*d^2)*D y = 0 := by
  have hh := congrArg D h
  simp only [map_add, Derivation.leibniz, derivation_square, map_zero, zero_add] at hh
  convert hh using 1
  simp only [smul_eq_mul]
  ring

end PermanentBorder.FrobeniusDVR

namespace PermanentBorder.FrobeniusDVR
open IsDiscreteValuationRing
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

lemma mem_ideal_of_valuation_product {I : Ideal B} {g f z : B}
    (hg : g ≠ 0) (h : I * Ideal.span {g} = Ideal.span {f})
    (hv : addVal B f ≤ addVal B g + addVal B z) : z ∈ I := by
  have hm : z*g ∈ I * Ideal.span {g} := by
    rw [h, Ideal.mem_span_singleton]
    apply (addVal_le_iff_dvd (R := B)).mp
    simpa only [addVal_mul, add_comm (addVal B z)] using hv
  obtain ⟨v,hv,he⟩ := Ideal.mem_mul_span_singleton.mp hm
  have he' : v = z := mul_right_cancel₀ hg he
  rwa [he'] at hv

end PermanentBorder.FrobeniusDVR

namespace PermanentBorder.FrobeniusDVR
open IsDiscreteValuationRing
variable {K B : Type*} [CommRing K] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra K B] [CharP B 2]
local notation "v" => addVal B

lemma gradient_valuation (D : Derivation K B B) (x y a b c d : B)
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    v (c^2+x*d^2) ≤ v (D x) + v (b^2+y*d^2) := by
  by_cases hdy : D y = 0
  · have hh := branch_chain D x y a b c d h
    rw [hdy,mul_zero,add_zero] at hh
    rcases mul_eq_zero.mp hh with hf|hx
    · simp [hf]
    · simp [hx]
  · have he := congrArg v (CharTwo.add_eq_zero.mp (branch_chain D x y a b c d h))
    rw [addVal_mul,addVal_mul] at he
    calc
      v (c^2+x*d^2) ≤ v (c^2+x*d^2) + v (D y) := le_add_of_nonneg_right zero_le
      _ = v (D x)+v (b^2+y*d^2) := by rw [← he,add_comm]

lemma radical_gradient_valuation (D : Derivation K B B) (x y a b c d z : B)
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0)
    (hz : z ∈ (Ideal.span {b^2+y*d^2,c^2+x*d^2}).radical) :
    v (c^2+x*d^2) ≤ v (D x) + v (d^2*z) := by
  by_cases hz1 : 1 ≤ v z
  · have hh := valuation_square_plus_le D x c d
    rw [addVal_mul,addVal_pow,nsmul_eq_mul]
    calc
      v (c^2+x*d^2) ≤ v (D x)+2*v d+1 := hh
      _ ≤ v (D x)+2*v d+v z := add_le_add le_rfl hz1
      _ = v (D x)+(2*v d+v z) := by ac_rfl
  · have hz0 : v z = 0 := by
      have hh := lt_of_not_ge hz1
      exact le_antisymm (Order.le_of_lt_add_one hh) zero_le
    have hzu : IsUnit z := (addVal_eq_zero_iff (R := B)).mp hz0
    have hI : Ideal.span {b^2+y*d^2,c^2+x*d^2} = ⊤ := by
      obtain ⟨n,hn⟩ := Ideal.mem_radical_iff.mp hz
      exact (Ideal.span {b^2+y*d^2,c^2+x*d^2}).eq_top_of_isUnit_mem hn (hzu.pow n)
    have hu : IsUnit (b^2+y*d^2) ∨ IsUnit (c^2+x*d^2) := by
      by_contra! hh
      have hm : Ideal.span {b^2+y*d^2,c^2+x*d^2} ≤ IsLocalRing.maximalIdeal B := by
        apply Ideal.span_le.mpr
        intro w hw
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
        rcases hw with rfl|rfl
        · exact hh.1
        · exact hh.2
      rw [hI] at hm
      exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp hm)
    rcases hu with hfx|hfy
    · have hh := gradient_valuation D x y a b c d h
      rw [(addVal_eq_zero_iff (R := B)).mpr hfx,add_zero] at hh
      exact hh.trans (le_add_of_nonneg_right zero_le)
    · rw [(addVal_eq_zero_iff (R := B)).mpr hfy]
      exact zero_le

theorem radical_gradient_conductor (D : Derivation K B B)
    (x y a b c d g : B) (C : Ideal B)
    (hx : D x = g) (hg : g ≠ 0)
    (hC : C * Ideal.span {g} = Ideal.span {c^2+x*d^2})
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    b^2+y*d^2 ∈ C ∧ c^2+x*d^2 ∈ C ∧
      ∀ z ∈ (Ideal.span {b^2+y*d^2,c^2+x*d^2}).radical, d^2*z ∈ C := by
  refine ⟨?_,?_,?_⟩
  · apply mem_ideal_of_valuation_product hg hC
    simpa only [hx] using gradient_valuation D x y a b c d h
  · apply mem_ideal_of_valuation_product hg hC
    exact le_add_of_nonneg_left zero_le
  · intro z hz
    apply mem_ideal_of_valuation_product hg hC
    simpa only [hx] using radical_gradient_valuation D x y a b c d z h hz

end PermanentBorder.FrobeniusDVR
namespace PermanentBorder.FrobeniusDVR
open IsDiscreteValuationRing
variable {K B : Type*} [CommRing K] [CommRing B] [IsDedekindDomain B]
  [Algebra K B] [CharP B 2]

theorem radical_gradient_conductor_dedekind (D : Derivation K B B)
    (x y a b c d g : B) (C : Ideal B)
    (hx : D x = g) (hg : g ≠ 0) (hC0 : C ≠ ⊥)
    (hC : C * Ideal.span {g} = Ideal.span {c^2+x*d^2})
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    b^2+y*d^2 ∈ C ∧ c^2+x*d^2 ∈ C ∧
      ∀ z ∈ (Ideal.span {b^2+y*d^2,c^2+x*d^2}).radical, d^2*z ∈ C := by
  have hloc (P : Ideal B) [P.IsMaximal] (hP : P ≠ ⊥) :
      let φ := algebraMap B (Localization.AtPrime P)
      φ (b^2+y*d^2) ∈ C.map φ ∧ φ (c^2+x*d^2) ∈ C.map φ ∧
        ∀ z ∈ (Ideal.span {b^2+y*d^2,c^2+x*d^2}).radical,
          φ (d^2*z) ∈ C.map φ := by
    let T := Localization.AtPrime P
    let φ := algebraMap B T
    have : IsDiscreteValuationRing T :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP T
    have hinj : Function.Injective φ := IsLocalization.injective T P.primeCompl_le_nonZeroDivisors
    have : CharP T 2 := charP_of_injective_algebraMap hinj 2
    let D' := NormalizationDerivation.extendEtale (T := T) D
    have hx' : D' (φ x) = φ g := by
      simp only [D',φ,NormalizationDerivation.extendEtale_algebraMap,hx]
    have hC' : C.map φ * Ideal.span {φ g} = Ideal.span {(φ c)^2+φ x*(φ d)^2} := by
      have hh := congrArg (Ideal.map φ) hC
      rw [Ideal.map_mul φ C (Ideal.span {g})] at hh
      simpa only [Ideal.map_span,Set.image_singleton,map_add,map_mul,map_pow] using hh
    have h' : (φ a)^2+φ x*(φ b)^2+φ y*(φ c)^2+φ x*φ y*(φ d)^2 = 0 := by
      simpa only [map_add,map_mul,map_pow,map_zero] using congrArg φ h
    obtain ⟨hfx,hfy,hz⟩ := radical_gradient_conductor D' (φ x) (φ y)
      (φ a) (φ b) (φ c) (φ d) (φ g) (C.map φ) hx' (by simpa only [map_zero] using hinj.ne hg) hC' h'
    refine ⟨by simpa only [map_add,map_mul,map_pow] using hfx,
      by simpa only [map_add,map_mul,map_pow] using hfy,?_⟩
    intro z hzm
    have hz' : φ z ∈ (Ideal.span {(φ b)^2+φ y*(φ d)^2,
        (φ c)^2+φ x*(φ d)^2}).radical := by
      have hh := Ideal.map_radical_le φ (Ideal.mem_map_of_mem φ hzm)
      simpa only [Ideal.map_span,Set.image_insert_eq,Set.image_singleton,
        map_add,map_mul,map_pow] using hh
    simpa only [map_mul,map_pow] using hz (φ z) hz'
  have hmem (z : B)
      (hz : ∀ (P : Ideal B) [P.IsMaximal], P ≠ ⊥ →
        algebraMap B (Localization.AtPrime P) z ∈
          C.map (algebraMap B (Localization.AtPrime P))) : z ∈ C := by
    apply Ideal.mem_of_localization_maximal
    intro P hP
    by_cases hP0 : P = ⊥
    · have hCt : C = ⊤ := by
        by_contra hCt
        exact hC0 ((hP.eq_of_le hCt (hP0 ▸ bot_le)).symm.trans hP0)
      exact Ideal.mem_map_of_mem _ (hCt ▸ Submodule.mem_top)
    · exact hz P hP0
  refine ⟨hmem _ (fun P _ hP => (hloc P hP).1),
    hmem _ (fun P _ hP => (hloc P hP).2.1),?_⟩
  intro z hz
  exact hmem _ (fun P _ hP => (hloc P hP).2.2 z hz)

end PermanentBorder.FrobeniusDVR
namespace PermanentBorder.ReducedBranchConductor
open Polynomial
section Branch
variable {K S Q L B : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed S] [IsLocalRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [FiniteDimensional Q L] [Algebra.IsSeparable Q L]
  [CommRing B] [IsDedekindDomain B] [IsPrincipalIdealRing B]
  [Algebra S B] [Module.Finite S B] [Algebra B L] [IsScalarTower S B L]
  [IsIntegralClosure B S L] [Module.IsTorsionFree S B]
  [Algebra K S] [Algebra K B] [IsScalarTower K S B] [CharP B 2]

include Q L in

theorem branch_conductor (δ : Derivation K S S) (x : S) (hx : δ x = 1)
    (y a b c d : B) (f w : S[X])
    (hygen : Algebra.adjoin Q {algebraMap B L y} = ⊤)
    (hfactor : f = minpoly S y * w)
    (hsep : (f.map (algebraMap S Q)).Separable)
    (hfy : aeval y f.derivative = c^2+algebraMap S B x*d^2)
    (h : a^2+algebraMap S B x*b^2+y*c^2+algebraMap S B x*y*d^2=0) :
    let J := conductor S y * Ideal.span {aeval y w}
    b^2+y*d^2 ∈ J ∧ c^2+algebraMap S B x*d^2 ∈ J ∧
      ∀ z ∈ (Ideal.span {b^2+y*d^2,c^2+algebraMap S B x*d^2}).radical,
        d^2*z ∈ J := by
  have hyf : aeval y f = 0 := by
    rw [hfactor,map_mul,minpoly.aeval,zero_mul]
  have hder0 : aeval y f.derivative ≠ 0 := by
    have hz : aeval (algebraMap B L y) (f.map (algebraMap S Q)) = 0 := by
      rw [aeval_map_algebraMap]
      change aeval ((IsScalarTower.toAlgHom S B L) y) f = 0
      rw [aeval_algHom_apply,hyf,map_zero]
    have hh := hsep.aeval_derivative_ne_zero hz
    intro he
    apply hh
    rw [derivative_map,aeval_map_algebraMap]
    change aeval ((IsScalarTower.toAlgHom S B L) y) f.derivative = 0
    rw [aeval_algHom_apply,he,map_zero]
  obtain ⟨g,D,hgD,hD⟩ :=
    NormalizationDerivation.exists_scaled_normalization_derivation (Q := Q) (L := L) (B := B) δ
  have hd : conductor S y * Ideal.span {g} = Ideal.span {aeval y (minpoly S y).derivative} := by
    rw [← hgD]
    exact conductor_mul_differentIdeal S Q L y hygen
  have hJ : (conductor S y * Ideal.span {aeval y w}) * Ideal.span {g} =
      Ideal.span {c^2+algebraMap S B x*d^2} := by
    rw [mul_right_comm,hd,Ideal.span_singleton_mul_span_singleton,← map_mul]
    rw [← hfy]
    congr 1
    simp only [hfactor,derivative_mul,map_add,map_mul,minpoly.aeval,zero_mul,add_zero]
  have hg : g ≠ 0 := by
    intro hg
    rw [hg,Ideal.span_singleton_zero,Ideal.mul_bot] at hJ
    have hz : c^2+algebraMap S B x*d^2=0 := Ideal.span_singleton_eq_bot.mp hJ.symm
    exact hder0 (hfy.trans hz)
  have hJ0 : conductor S y * Ideal.span {aeval y w} ≠ ⊥ := by
    intro hJ0
    rw [hJ0,Ideal.bot_mul] at hJ
    exact hder0 (hfy.trans (Ideal.span_singleton_eq_bot.mp hJ.symm))
  apply FrobeniusDVR.radical_gradient_conductor_dedekind D
    (algebraMap S B x) y a b c d g _ _ hg hJ0 hJ h
  rw [hD,hx,map_one,mul_one]
end Branch
end PermanentBorder.ReducedBranchConductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.BranchConductor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.ReducedBranchConductor
open Polynomial

section Ideal
variable {S : Type*} [CommRing S]

variable {B : Type*} [CommRing B] [Algebra S B]
lemma map_enlarged_le (f b c d : S[X]) (x : S) (y : B) (J : Ideal B)
    (hf : aeval y f = 0)
    (hb : aeval y (b^2+X*d^2) ∈ J)
    (hc : aeval y (c^2+C x*d^2) ∈ J)
    (hr : ∀ z ∈ (Ideal.span {aeval y (b^2+X*d^2),aeval y (c^2+C x*d^2)}).radical,
      (aeval y d)^2*z ∈ J) :
    enlargedGradientIdeal f b c d x ≤ Ideal.comap (aeval y) J := by
  let H : Ideal B := Ideal.span {aeval y (b^2+X*d^2),aeval y (c^2+C x*d^2)}
  have hi : gradientIdeal f b c d x ≤ Ideal.comap (aeval y) H := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with hz|hz|hz
    · rw [hz]
      change aeval y f ∈ H
      rw [hf]; exact H.zero_mem
    · rw [hz]; exact Ideal.subset_span (by simp)
    · rw [hz]; exact Ideal.subset_span (by simp)
  have hir : (gradientIdeal f b c d x).radical ≤ Ideal.comap (aeval y) H.radical := by
    rw [Ideal.comap_radical]
    exact Ideal.radical_mono hi
  apply sup_le
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with hz|hz|hz
    · rw [hz]
      change aeval y f ∈ J
      rw [hf]; exact J.zero_mem
    · rw [hz]; exact hb
    · rw [hz]; exact hc
  · rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    change aeval y (d^2*z) ∈ J
    rw [map_mul,map_pow]
    exact hr _ (hir hz)
end Ideal

section Field
variable {Q : Type*} [Field Q]
lemma root_generates (p : Q[X]) : Algebra.adjoin Q {AdjoinRoot.root p} = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval,AlgHom.range_eq_top]
  intro z
  obtain ⟨q,hq⟩ := AdjoinRoot.mk_surjective z
  exact ⟨q,by rw [AdjoinRoot.aeval_eq]; exact hq⟩

lemma root_separable (p : Q[X]) [Fact (Irreducible p)] (hsep : p.Separable) :
    Algebra.IsSeparable Q (AdjoinRoot p) := by
  have hp0 : p ≠ 0 := (Fact.out : Irreducible p).ne_zero
  have hr : IsSeparable Q (AdjoinRoot.root p) := hsep.of_dvd
    (minpoly.dvd Q _ (AdjoinRoot.eval₂_root p))
  have hl : Algebra.adjoin Q {AdjoinRoot.root p} ≤ (separableClosure Q (AdjoinRoot p)).toSubalgebra :=
    Algebra.adjoin_le (by intro z hz; obtain rfl := Set.mem_singleton_iff.mp hz; exact hr)
  rw [root_generates] at hl
  exact ⟨fun z => hl (show z ∈ (⊤ : Subalgebra Q (AdjoinRoot p)) from trivial)⟩
end Field

section Realization
variable {K S Q : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsPrincipalIdealRing S] [IsLocalRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
  [Algebra K S] [CharP S 2]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]

include K in

theorem irreducible_realization (δ : Derivation K S S) (x : S) (hx : δ x=1)
    (f p w a b c d : S[X]) (hp : p.Monic)
    (hir : Irreducible (p.map (algebraMap S Q)))
    (hfactor : f=p*w) (hsep : (f.map (algebraMap S Q)).Separable)
    (hsq : f=a^2+C x*b^2+X*c^2+C x*X*d^2)
    (hder : f.derivative=c^2+C x*d^2)
    (z : S[X]) (hz : z ∈ enlargedGradientIdeal f b c d x)
    (t : AdjoinRoot (p.map (algebraMap S Q))) (ht : IsIntegral S t) :
    ∃ q : S[X], AdjoinRoot.mk (p.map (algebraMap S Q)) ((w*q).map (algebraMap S Q)) =
      AdjoinRoot.mk (p.map (algebraMap S Q)) (z.map (algebraMap S Q))*t := by
  let pg := p.map (algebraMap S Q)
  let : Fact (Irreducible pg) := ⟨hir⟩
  let L := AdjoinRoot pg
  let B := integralClosure S L
  let : Algebra K B := Algebra.compHom B (algebraMap K S)
  let : IsScalarTower K S B := IsScalarTower.of_algebraMap_eq' rfl
  have hps : pg.Separable := hsep.of_dvd (Polynomial.map_dvd _ (hfactor ▸ dvd_mul_right p w))
  let : Algebra.IsSeparable Q L := root_separable pg hps
  let : FiniteDimensional Q L := (AdjoinRoot.powerBasis hir.ne_zero).finite
  let : IsDedekindDomain B := integralClosure.isDedekindDomain S Q L
  let : Module.Finite S B := IsIntegralClosure.finite S Q L B
  let : IsPrincipalIdealRing B := Conductor.integralClosure_isPrincipalIdealRing (S := S) (Q := Q) (L := L)
  have hsL : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S Q L]
    exact (algebraMap Q L).injective.comp (IsFractionRing.injective S Q)
  have hsB : Function.Injective (algebraMap S B) := by
    intro a b h
    apply hsL
    simpa only [IsScalarTower.algebraMap_apply S B L] using congrArg (algebraMap B L) h
  let : CharP B 2 := charP_of_injective_algebraMap hsB 2
  let : Module.IsTorsionFree S B := (Module.isTorsionFree_iff_algebraMap_injective).mpr hsB
  have hyi : IsIntegral S (AdjoinRoot.root pg) := ⟨p,hp,by
    change aeval (AdjoinRoot.root pg) p = 0
    rw [AdjoinRoot.aeval_eq_of_algebra]
    exact AdjoinRoot.mk_self⟩
  let y : B := IsIntegralClosure.mk' B (AdjoinRoot.root pg) hyi
  have hy : algebraMap B L y = AdjoinRoot.root pg := IsIntegralClosure.algebraMap_mk' B _ hyi
  have hyint : IsIntegral S y := IsIntegralClosure.isIntegral S L y
  have hmin : minpoly S y = p := by
    apply Polynomial.map_injective _ (IsFractionRing.injective S Q)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions Q L hyint,hy,
      AdjoinRoot.minpoly_root hir.ne_zero,(hp.map _).leadingCoeff,inv_one,C_1,mul_one]
  have hygen : Algebra.adjoin Q {algebraMap B L y} = ⊤ := by rw [hy]; exact root_generates pg
  have hfy : aeval y f = 0 := by rw [hfactor,← hmin,map_mul,minpoly.aeval,zero_mul]
  have hsq' : (aeval y a)^2+algebraMap S B x*(aeval y b)^2+y*(aeval y c)^2+
      algebraMap S B x*y*(aeval y d)^2=0 := by
    simpa only [hsq,map_add,map_mul,map_pow,aeval_C,aeval_X] using hfy
  obtain ⟨hb,hc,hr⟩ := branch_conductor (Q := Q) (L := L) δ x hx y
    (aeval y a) (aeval y b) (aeval y c) (aeval y d) f w hygen
    (by rw [hmin]; exact hfactor) hsep (by simp only [hder,map_add,map_mul,map_pow,aeval_C]) hsq'
  have hm : aeval y z ∈ conductor S y * Ideal.span {aeval y w} := by
    change z ∈ Ideal.comap (aeval y) (conductor S y * Ideal.span {aeval y w})
    apply map_enlarged_le f b c d x y _ hfy ?_ ?_ ?_ hz
    · simpa only [map_add,map_mul,map_pow,aeval_X] using hb
    · simpa only [map_add,map_mul,map_pow,aeval_C] using hc
    · simpa only [map_add,map_mul,map_pow,aeval_X,aeval_C] using hr
  obtain ⟨u,hu,he⟩ := Ideal.mem_mul_span_singleton.mp hm
  let t' : B := IsIntegralClosure.mk' B t ht
  have hur := mem_conductor_iff.mp hu t'
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hur
  obtain ⟨q,hq⟩ := hur
  change aeval y q = u*t' at hq
  refine ⟨q,?_⟩
  have hzb : aeval y (w*q) = aeval y z*t' := by
    rw [map_mul,hq,← he]
    ring
  have hh := congrArg (algebraMap B L) hzb
  have hev (v : S[X]) : algebraMap B L (aeval y v) =
      AdjoinRoot.mk pg (v.map (algebraMap S Q)) := by
    change (IsScalarTower.toAlgHom S B L) (aeval y v) = _
    rw [← aeval_algHom_apply]
    change aeval (algebraMap B L y) v = _
    rw [hy,AdjoinRoot.aeval_eq_of_algebra]
  rw [map_mul (algebraMap B L),hev,hev,IsIntegralClosure.algebraMap_mk'] at hh
  exact hh
end Realization
end PermanentBorder.ReducedBranchConductor
namespace PermanentBorder.FactorNormalization
open Polynomial UniqueFactorizationMonoid
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]

omit [IsDomain S] in

lemma lift_monic_factor {f : S[X]} (hf : f.Monic) {p : Q[X]}
    (hp : p.Monic) (hd : p ∣ (f).map (algebraMap S Q)) :
    ∃ q : S[X], q.Monic ∧ q.map (algebraMap S Q) = p := by
  obtain ⟨q,hq⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Q hf hd
  rw [hp.leadingCoeff,C_1,mul_one] at hq
  exact ⟨q,Polynomial.monic_of_injective (IsFractionRing.injective S Q)
    (hq ▸ hp),hq⟩

omit [IsDomain S] in

theorem exists_factors {f : S[X]} (hf : f.Monic)
    (hsep : ((f).map (algebraMap S Q)).Separable) :
    ∃ (s : Finset Q[X]) (p : s → S[X]),
      (∀ i, (p i).Monic ∧ (p i).map (algebraMap S Q) = i.val ∧ Irreducible i.val) ∧
      (∏ i, p i) = f := by
  classical
  let g := (f).map (algebraMap S Q)
  have hg : g.Monic := hf.map _
  let s : Finset Q[X] := ⟨normalizedFactors g,
    (squarefree_iff_nodup_normalizedFactors hg.ne_zero).mp hsep.squarefree⟩
  have hi (i : s) : Irreducible i.val ∧ i.val.Monic ∧ i.val ∣ g :=
    (Polynomial.mem_normalizedFactors_iff hg.ne_zero).mp i.property
  choose p hpm hpe using fun i : s => lift_monic_factor hf (hi i).2.1 (hi i).2.2
  refine ⟨s,p,fun i => ⟨hpm i,hpe i,(hi i).1⟩,?_⟩
  apply Polynomial.map_injective _ (IsFractionRing.injective S Q)
  rw [Polynomial.map_prod]
  simp_rw [hpe]
  have hp := leadingCoeff_mul_prod_normalizedFactors g
  rw [hg.leadingCoeff,C_1,one_mul] at hp
  change (∏ i : s, id (i : Q[X])) = g
  rw [Finset.prod_coe_sort]
  change ((normalizedFactors g).map id).prod = g
  simpa using hp

section Cofactors
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → S[X])

omit [IsDomain S] [IsIntegrallyClosed S] in
lemma factor_mul_cofactor (i : ι) : p i * cofactor p i = ∏ j, p j := by
  classical
  exact Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)

omit [IsDomain S] [IsIntegrallyClosed S] in
lemma cofactor_dvd_of_ne {i j : ι} (h : i ≠ j) : p j ∣ cofactor p i := by
  classical
  apply Finset.dvd_prod_of_mem
  simp only [Finset.mem_erase,Finset.mem_univ,and_true]
  exact h.symm

end Cofactors
end PermanentBorder.FactorNormalization

namespace PermanentBorder.FactorNormalization
open Polynomial
section Reconstruct
variable {S Q ι : Type*} [CommRing S] [Field Q] [Algebra S Q]
  [Fintype ι] [DecidableEq ι]
variable (p : ι → S[X])
local notation "f" => ∏ i, p i
local notation "pQ" => fun i => Polynomial.map (algebraMap S Q) (p i)

omit [DecidableEq ι] in
lemma components_injective
    (hcop : Pairwise (fun i j => IsCoprime (pQ i) (pQ j))) :
    Function.Injective (fun z => fun i => component (Q := Q) p i z) := by
  intro z w h
  have hz : ∀ i, component p i (z-w) = 0 := by
    intro i
    rw [map_sub,sub_eq_zero]
    exact congrFun h i
  suffices z-w=0 from sub_eq_zero.mp this
  obtain ⟨q,hq⟩ := AdjoinRoot.mk_surjective (z-w)
  rw [← hq,AdjoinRoot.mk_eq_zero]
  rw [Polynomial.map_prod]
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact hcop hij
  · intro i _
    apply AdjoinRoot.mk_eq_zero.mp
    simpa only [← hq,component_mk] using hz i

theorem reconstruct (hcop : Pairwise (fun i j => IsCoprime (pQ i) (pQ j)))
    (z : AdjoinRoot ((f).map (algebraMap S Q))) (q : ι → S[X])
    (hz : ∀ i, component p i z =
      AdjoinRoot.mk (pQ i) ((cofactor p i * q i).map (algebraMap S Q))) :
    AdjoinRoot.mk ((f).map (algebraMap S Q))
      ((∑ i, cofactor p i*q i).map (algebraMap S Q)) = z := by
  apply components_injective p hcop
  funext i
  dsimp only
  rw [component_mk,Polynomial.map_sum,map_sum]
  rw [Finset.sum_eq_single i]
  · exact (hz i).symm
  · intro j _ hji
    apply AdjoinRoot.mk_eq_zero.mpr
    exact Polynomial.map_dvd (algebraMap S Q)
      (dvd_mul_of_dvd_left (cofactor_dvd_of_ne p hji) (q j))
  · intro hi
    exact (hi (Finset.mem_univ i)).elim
end Reconstruct
end PermanentBorder.FactorNormalization
namespace PermanentBorder.ReducedBranchConductor
open Polynomial FactorNormalization
section
variable {K S Q : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsPrincipalIdealRing S] [IsLocalRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
  [Algebra K S] [CharP S 2]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]

include K in

theorem reduced_local_realization (δ : Derivation K S S) (x : S) (hx : δ x=1)
    (f a b c d : S[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap S Q)).Separable)
    (hsq : f=a^2+C x*b^2+X*c^2+C x*X*d^2)
    (hder : f.derivative=c^2+C x*d^2)
    (z : S[X]) (hz : z ∈ enlargedGradientIdeal f b c d x)
    (t : AdjoinRoot (f.map (algebraMap S Q))) (ht : IsIntegral S t) :
    ∃ q : S[X], AdjoinRoot.mk (f.map (algebraMap S Q)) (q.map (algebraMap S Q)) =
      AdjoinRoot.mk (f.map (algebraMap S Q)) (z.map (algebraMap S Q))*t := by
  classical
  obtain ⟨s,p,hp,hprod⟩ := exists_factors hf hsep
  subst hprod
  have hfac (i : s) : (∏ j, p j) = p i * cofactor p i := (factor_mul_cofactor p i).symm
  have hcop : Pairwise (fun i j => IsCoprime
      ((p i).map (algebraMap S Q)) ((p j).map (algebraMap S Q))) := by
    intro i j hij
    have hh := hsep
    rw [hfac i,Polynomial.map_mul] at hh
    exact hh.isCoprime.of_isCoprime_of_dvd_right (Polynomial.map_dvd _ (cofactor_dvd_of_ne p hij))
  have ht' (i : s) : IsIntegral S (component (Q := Q) p i t) :=
    ht.map ((component (Q := Q) p i).restrictScalars S)
  have hr (i : s) := irreducible_realization δ x hx (∏j,p j) (p i) (cofactor p i)
    a b c d (hp i).1 (by rw [(hp i).2.1]; exact (hp i).2.2)
    (hfac i) hsep hsq hder z hz (component (Q := Q) p i t) (ht' i)
  choose q hq using hr
  refine ⟨∑ i, cofactor p i*q i,?_⟩
  apply reconstruct p hcop
  intro i
  rw [map_mul,component_mk]
  exact (hq i).symm
end
end PermanentBorder.ReducedBranchConductor
namespace PermanentBorder.ReducedBranchConductor
open Polynomial

section BaseChange
variable {S U : Type*} [CommRing S] [CommRing U] (ρ : S →+* U)

lemma gradient_map (f b c d : S[X]) (x : S) :
    Ideal.map (Polynomial.mapRingHom ρ) (gradientIdeal f b c d x) =
      gradientIdeal (f.map ρ) (b.map ρ) (c.map ρ) (d.map ρ) (ρ x) := by
  simp only [gradientIdeal,Ideal.map_span,Set.image_insert_eq,Set.image_singleton,
    coe_mapRingHom,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C]

lemma enlarged_map_le (f b c d : S[X]) (x : S) :
    Ideal.map (Polynomial.mapRingHom ρ) (enlargedGradientIdeal f b c d x) ≤
      enlargedGradientIdeal (f.map ρ) (b.map ρ) (c.map ρ) (d.map ρ) (ρ x) := by
  rw [enlargedGradientIdeal,Ideal.map_sup,Ideal.map_mul,gradient_map]
  apply sup_le_sup le_rfl
  apply Ideal.mul_mono
  · simp only [Ideal.map_span,Set.image_singleton,coe_mapRingHom,Polynomial.map_pow]
    exact le_rfl
  · exact (Ideal.map_radical_le (Polynomial.mapRingHom ρ)).trans_eq (congrArg Ideal.radical (gradient_map ρ f b c d x))

end BaseChange

section LocalGlobal
variable {S Q : Type*} [CommRing S] [Field Q] [Algebra S Q]

lemma genericChange_mk (U : Type*) [CommRing U] [Algebra S U] [Algebra U Q]
    [IsScalarTower S U Q] (f p : S[X]) :
    genericChange U f (AdjoinRoot.mk _ (p.map (algebraMap S Q))) =
      AdjoinRoot.mk _ ((p.map (algebraMap S U)).map (algebraMap U Q)) := by
  have he : (genericChange (Q := Q) U f).toAlgHom.comp
      (AdjoinRoot.mkₐ (f.map (algebraMap S Q))) =
      AdjoinRoot.mkₐ ((f.map (algebraMap S U)).map (algebraMap U Q)) := by
    ext
    exact AdjoinRoot.algEquivOfEq_root _ _ (map_tower U f)
  rw [← map_tower U p]
  exact AlgHom.congr_fun he _

end LocalGlobal

section Lattice
variable {S : Type*} [CommRing S] [IsDomain S]
local notation "Q" => FractionRing S

lemma polynomial_lattice_local_global (f : S[X])
    (t : AdjoinRoot (f.map (algebraMap S Q)))
    (hlocal : ∀ (P : Ideal S) [P.IsMaximal],
      ∃ q : (Localization.AtPrime P)[X],
        AdjoinRoot.mk _ (q.map (algebraMap (Localization.AtPrime P) Q)) =
          genericChange (Localization.AtPrime P) f t) :
    ∃ q : S[X], AdjoinRoot.mk _ (q.map (algebraMap S Q)) = t := by
  let E := AdjoinRoot (f.map (algebraMap S Q))
  let j : S[X] →ₐ[S] E := (AdjoinRoot.mkₐ _).restrictScalars S |>.comp
    (Polynomial.mapAlgHom (Algebra.ofId S Q))
  let N : Submodule S E := LinearMap.range j.toLinearMap
  let D : Ideal S := Submodule.comap (LinearMap.toSpanSingleton S E t) N
  have hD : D = ⊤ := by
    by_contra hn
    obtain ⟨P,hP,hDP⟩ := Ideal.exists_le_maximal D hn
    let := hP
    let U := Localization.AtPrime P
    obtain ⟨q,hq⟩ := hlocal P
    obtain ⟨s,hs,hsp⟩ := IsLocalization.integerNormalization_spec P.primeCompl q
    have hst : (s : S) • t ∈ N := by
      refine ⟨IsLocalization.integerNormalization P.primeCompl q,?_⟩
      change j _ = s • t
      apply (genericChange U f).injective
      change genericChange U f (AdjoinRoot.mk _ ((IsLocalization.integerNormalization P.primeCompl q).map (algebraMap S Q))) = _
      rw [genericChange_mk,hsp]
      change ((AdjoinRoot.mkₐ _).restrictScalars S)
        (((Polynomial.mapAlgHom (Algebra.ofId U Q)).restrictScalars S) (s • q)) =
        ((genericChange U f).restrictScalars S) (s • t)
      rw [map_smul,map_smul,map_smul]
      exact congrArg (fun u => s • u) hq

    have hsD : s ∈ D := hst
    exact hs (hDP hsD)
  have ht : t ∈ N := by
    have hh : (1:S) ∈ D := by rw [hD]; trivial
    simpa only [D,Submodule.mem_comap,LinearMap.toSpanSingleton_apply,one_smul] using hh
  exact ht
end Lattice

section Residue
variable {K : Type*} [Field K] [IsAlgClosed K]
lemma polynomial_residue_algClosed (P : Ideal K[X]) [P.IsMaximal] :
    IsAlgClosed P.ResidueField := by
  let : Algebra.FiniteType K P.ResidueField := Algebra.FiniteType.of_surjective
    (IsScalarTower.toAlgHom K K[X] P.ResidueField) P.algebraMap_residueField_surjective
  let : Module.Finite K P.ResidueField := finite_of_finite_type_of_isJacobsonRing K P.ResidueField
  exact IsAlgClosed.of_ringEquiv K _ (RingEquiv.ofBijective (algebraMap K P.ResidueField)
    IsAlgClosed.algebraMap_bijective_of_isIntegral)
end Residue
section Global
variable {K S : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsPrincipalIdealRing S] [Algebra K S] [CharP S 2]
local notation "Q" => FractionRing S

theorem reduced_global_realization (δ : Derivation K S S) (x : S) (hx : δ x = 1)
    (hres : ∀ (P : Ideal S) [P.IsMaximal], IsAlgClosed P.ResidueField)
    (f a b c d : S[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap S Q)).Separable)
    (hsq : f=a^2+C x*b^2+X*c^2+C x*X*d^2)
    (hder : f.derivative=c^2+C x*d^2)
    (z : S[X]) (hz : z ∈ enlargedGradientIdeal f b c d x)
    (t : AdjoinRoot (f.map (algebraMap S Q))) (ht : IsIntegral S t) :
    ∃ q : S[X], AdjoinRoot.mk _ (q.map (algebraMap S Q)) =
      AdjoinRoot.mk _ (z.map (algebraMap S Q))*t := by
  apply polynomial_lattice_local_global
  intro P hP
  let U := Localization.AtPrime P
  let : IsAlgClosed (IsLocalRing.ResidueField U) := hres P
  let : CharP U 2 := charP_of_injective_algebraMap
    (IsLocalization.injective U P.primeCompl_le_nonZeroDivisors) 2
  let ρ := algebraMap S U
  let δ' := NormalizationDerivation.extendEtale (T := U) δ
  have hx' : δ' (ρ x) = 1 := by
    rw [NormalizationDerivation.extendEtale_algebraMap,hx,map_one]
  have ht' : IsIntegral U (genericChange U f t) :=
    (ht.map ((genericChange U f).restrictScalars S).toAlgHom).tower_top
  have hs' : (f.map ρ)= (a.map ρ)^2+C (ρ x)*(b.map ρ)^2+
      X*(c.map ρ)^2+C (ρ x)*X*(d.map ρ)^2 := by
    rw [hsq]
    simp only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_X]
  have hd' : (f.map ρ).derivative = (c.map ρ)^2+C (ρ x)*(d.map ρ)^2 := by
    rw [Polynomial.derivative_map,hder]
    simp only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_C]
  have hz' : z.map ρ ∈ enlargedGradientIdeal (f.map ρ) (b.map ρ) (c.map ρ) (d.map ρ) (ρ x) :=
    enlarged_map_le ρ f b c d x (Ideal.mem_map_of_mem (Polynomial.mapRingHom ρ) hz)
  obtain ⟨q,hq⟩ := reduced_local_realization δ' (ρ x) hx' (f.map ρ) (a.map ρ)
    (b.map ρ) (c.map ρ) (d.map ρ) (hf.map ρ) (by rw [← map_tower U f]; exact hsep)
    hs' hd' (z.map ρ) hz' (genericChange U f t) ht'
  refine ⟨q,?_⟩
  rw [map_mul,genericChange_mk]
  exact hq
end Global
end PermanentBorder.ReducedBranchConductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PlaneHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

lemma finrank_piece (d : ℤ) : Module.finrank K (H (K := K) d) = (d+1).toNat := by
  rw [(pieceCoordinates d).finrank_eq, Module.finrank_pi]
  by_cases hd : 0 ≤ d
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [Fintype.card_congr (degreeIndexEquiv n), Fintype.card_fin]
    omega
  · have : IsEmpty (DegreeIndex (Fin 2) d) := ⟨fun s => by
      have hs : (0 : ℤ) ≤ s.val.degree := by positivity
      exact hd (s.property ▸ hs)⟩
    have hc : Fintype.card (DegreeIndex (Fin 2) d) = 0 := Fintype.card_eq_zero
    rw [hc]
    omega

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

lemma varMul_injective (i : Fin 2) (n : ℕ) :
    Function.Injective (varMul (K := K) i n) := by
  intro p q h
  apply Subtype.ext
  exact mul_left_cancel₀ (X_ne_zero i) (congrArg Subtype.val h)

lemma piece_degreeOf_le {n : ℕ} (p : H (K := K) (n : ℤ)) (i : Fin 2) :
    p.val.degreeOf i ≤ n :=
  (degreeOf_le_totalDegree _ _).trans (intWeight_homogeneous p.property).totalDegree_le

theorem exists_varMul_outside {n : ℕ} (W : Submodule K (H (K := K) (n : ℤ)))
    (hW : W ≠ ⊥) :
    ∃ p ∈ W, varMul 0 n p ∉ W.map (varMul 1 n) := by
  classical
  obtain ⟨p,hp,hp0⟩ := W.ne_bot_iff.mp hW
  have hpv : p.val ≠ 0 := fun h => hp0 (Subtype.ext h)
  let P : ℕ → Prop := fun j => ∃ v ∈ W, v.val ≠ 0 ∧ v.val.degreeOf 0 = j
  have he : P (p.val.degreeOf 0) := ⟨p,hp,hpv,rfl⟩
  have hb := piece_degreeOf_le p 0
  obtain ⟨q,hq,hq0,hqm⟩ := Nat.findGreatest_spec hb he
  refine ⟨q,hq,?_⟩
  rintro ⟨z,hz,heq⟩
  have hz0 : z.val ≠ 0 := by
    intro h
    have hh := congrArg Subtype.val heq
    change X 1 * z.val = X 0 * q.val at hh
    rw [h,mul_zero] at hh
    exact (mul_ne_zero (X_ne_zero 0) hq0) hh.symm
  have hzm : z.val.degreeOf 0 ≤ Nat.findGreatest P n :=
    Nat.le_findGreatest (piece_degreeOf_le z 0) ⟨z,hz,hz0,rfl⟩
  have hh := congrArg (fun v : H (K := K) ((n+1 : ℕ) : ℤ) => v.val.degreeOf 0) heq
  change (X 1 * z.val).degreeOf 0 = (X 0 * q.val).degreeOf 0 at hh
  rw [mul_comm (X 1), degreeOf_mul_X_of_ne _ (by decide : (0 : Fin 2) ≠ 1),
    mul_comm (X 0), (degreeOf_mul_X_eq_degreeOf_add_one_iff 0 q.val).mpr hq0] at hh
  omega

lemma finrank_varMul_sup {n : ℕ} (W : Submodule K (H (K := K) (n : ℤ)))
    (hW : W ≠ ⊥) :
    Module.finrank K W + 1 ≤
      Module.finrank K ↥(W.map (varMul 0 n) ⊔ W.map (varMul 1 n)) := by
  obtain ⟨p,hp,hnot⟩ := exists_varMul_outside W hW
  have hlt : W.map (varMul 1 n) < W.map (varMul 0 n) ⊔ W.map (varMul 1 n) := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    apply hnot
    rw [heq]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hp)
  have hf := Submodule.finrank_strictMono hlt
  dsimp only at hf
  rw [← (Submodule.equivMapOfInjective (varMul 1 n) (varMul_injective 1 n) W).finrank_eq] at hf
  omega

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

lemma homogeneous_factor_right {a b : Plane (K := K)} {e t : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (h0 : a ≠ 0)
    (hab : (a*b).IsWeightedHomogeneous weight t) :
    b.IsWeightedHomogeneous weight (t-e) := by
  have hh := weightedHomogeneousComponent_eq_self hab
  rw [project_mul weight ha] at hh
  have hb : weightedHomogeneousComponent weight (t-e) b = b := mul_left_cancel₀ h0 hh
  rw [← hb]
  exact weightedHomogeneousComponent_mem weight b (t-e)

lemma mulPiece_injective {a : Plane (K := K)} {e : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (ha0 : a ≠ 0) (t : ℤ) :
    Function.Injective (mulPiece weight ha t) := by
  intro p q h
  apply Subtype.ext
  exact mul_left_cancel₀ ha0 (congrArg Subtype.val h)

lemma finrank_multiplicationRange {a : Plane (K := K)} {e : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (ha0 : a ≠ 0) (t : ℤ) :
    Module.finrank K (multiplicationRange ha t) = (t-e+1).toNat := by
  rw [LinearMap.finrank_range_of_inj (mulPiece_injective ha ha0 t), finrank_piece]

lemma multiplicationRange_inf {a b : Plane (K := K)} {e f : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (hb : b.IsWeightedHomogeneous weight f)
    (hb0 : b ≠ 0) (hab : IsRelPrime a b) (t : ℤ) :
    multiplicationRange ha t ⊓ multiplicationRange hb t =
      multiplicationRange (ha.mul hb) t := by
  ext p
  constructor
  · rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    have huv : a*u.val = b*v.val := congrArg Subtype.val (hu.trans hv.symm)
    have hd : b ∣ u.val := hab.symm.dvd_of_dvd_mul_left ⟨v,huv⟩
    obtain ⟨w,hw⟩ := hd
    have hbw : (b*w).IsWeightedHomogeneous weight (t-e) := hw ▸ u.property
    have hwh := homogeneous_factor_right hb hb0 hbw
    have hh : (t-e)-f = t-(e+f) := by ring
    rw [hh] at hwh
    refine ⟨⟨w,hwh⟩,?_⟩
    apply Subtype.ext
    change (a*b)*w = p.val
    rw [mul_assoc, ← hw]
    exact congrArg Subtype.val hu
  · rintro ⟨w,hw⟩
    have hbw : (b*w.val).IsWeightedHomogeneous weight (t-e) := by
      convert hb.mul w.property using 1; ring
    have haw : (a*w.val).IsWeightedHomogeneous weight (t-f) := by
      convert ha.mul w.property using 1; ring
    constructor
    · refine ⟨⟨b*w.val,hbw⟩,?_⟩
      apply Subtype.ext
      change a*(b*w.val) = p.val
      rw [← mul_assoc]
      exact congrArg Subtype.val hw
    · refine ⟨⟨a*w.val,haw⟩,?_⟩
      apply Subtype.ext
      change b*(a*w.val) = p.val
      rw [← mul_assoc, mul_comm b a]
      exact congrArg Subtype.val hw

end PermanentBorder.PlaneHilbert

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.FilteredPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma mem_filtered_succ (q : Plane (K := K) →ₐ[K] R) (n : ℕ) (z : R) :
    z ∈ filtered q (n+1) ↔ ∃ p : Plane (K := K), p.totalDegree ≤ n ∧ q p = z := by
  simp only [filtered,Submodule.mem_map,mem_restrictTotalDegree,AlgHom.toLinearMap_apply]

lemma filtered_mono (q : Plane (K := K) →ₐ[K] R) : Monotone (filtered q) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => exact bot_le
  | succ n =>
    intro z hz
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n z).mp hz
    exact (mem_filtered_succ q (n+1) _).mpr ⟨p,by omega,rfl⟩

lemma homogeneous_mem_filtered (q : Plane (K := K) →ₐ[K] R) {n : ℕ}
    (p : H (K := K) (n : ℤ)) : q p.val ∈ filtered q (n+1) := by
  exact (mem_filtered_succ q n _).mpr
    ⟨p.val,(intWeight_homogeneous p.property).totalDegree_le,rfl⟩

lemma mul_X_filtered (q : Plane (K := K) →ₐ[K] R) (i : Fin 2) {n : ℕ}
    {z : R} (hz : z ∈ filtered q n) : q (X i) * z ∈ filtered q (n+1) := by
  cases n with
  | zero =>
    have hz0 : z = 0 := hz
    simp [hz0]
  | succ n =>
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n z).mp hz
    apply (mem_filtered_succ q (n+1) _).mpr
    refine ⟨X i*p,?_,map_mul _ _ _⟩
    have hx : (X i : Plane (K := K)).totalDegree = 1 := totalDegree_X i
    exact (totalDegree_mul _ _).trans (by rw [hx]; omega)

lemma sub_topComponent_degree {p : Plane (K := K)} {n : ℕ}
    (hp : p.totalDegree ≤ n+1) : (p-(topComponent (n+1) p).val).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro s hs
  have hc : (p-(topComponent (n+1) p).val).coeff s ≠ 0 := mem_support_iff.mp hs
  change s.degree ≤ n
  by_contra! hn
  apply hc
  change (p-homogeneousComponent (n+1) p).coeff s = 0
  rw [coeff_sub,coeff_homogeneousComponent]
  by_cases he : s.degree = n+1
  · simp [he]
  · have hlt : p.totalDegree < s.degree := by omega
    simp [he,coeff_eq_zero_of_totalDegree_lt hlt]

lemma sub_topComponent_mem_filtered (q : Plane (K := K) →ₐ[K] R)
    {p : Plane (K := K)} {n : ℕ} (hp : p.totalDegree ≤ n) :
    q p - q (topComponent n p).val ∈ filtered q n := by
  cases n with
  | zero =>
    have he : p = (topComponent 0 p).val := by
      change p = homogeneousComponent 0 p
      rw [homogeneousComponent_zero]
      exact (totalDegree_eq_zero_iff_eq_C).mp (Nat.eq_zero_of_le_zero hp)
    rw [← he, sub_self]
    exact (filtered q 0).zero_mem
  | succ n =>
    exact (mem_filtered_succ q n _).mpr
      ⟨p-(topComponent (n+1) p).val,sub_topComponent_degree hp,map_sub _ _ _⟩

lemma mem_leadingRelations (q : Plane (K := K) →ₐ[K] R) (n : ℕ)
    (p : H (K := K) (n : ℤ)) : p ∈ leadingRelations q n ↔ q p.val ∈ filtered q n := by
  simp only [leadingRelations,LinearMap.mem_ker,leadingMap,LinearMap.comp_apply,
    Submodule.subtype_apply,AlgHom.toLinearMap_apply,Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

lemma varMul_leadingRelations (q : Plane (K := K) →ₐ[K] R) (i : Fin 2) (n : ℕ) :
    (leadingRelations q n).map (varMul i n) ≤ leadingRelations q (n+1) := by
  rintro _ ⟨p,hp,rfl⟩
  change p ∈ leadingRelations q n at hp
  rw [mem_leadingRelations] at hp ⊢
  change q (X i*p.val) ∈ _
  rw [map_mul]
  exact mul_X_filtered q i hp

lemma leadingMap_range (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    LinearMap.range (leadingMap q n) = (filtered q (n+1)).map (filtered q n).mkQ := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨q p.val,homogeneous_mem_filtered q p,rfl⟩
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n r).mp hr
    refine ⟨topComponent n p,?_⟩
    change Submodule.Quotient.mk (q (topComponent n p).val) = Submodule.Quotient.mk (q p)
    apply (Submodule.Quotient.eq _).mpr
    simpa only [neg_sub] using (filtered q n).neg_mem (sub_topComponent_mem_filtered q hp)

lemma filteredH_add_rank (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    filteredH q n + Module.finrank K (filtered q n) = Module.finrank K (filtered q (n+1)) := by
  let f := (filtered q n).mkQ.domRestrict (filtered q (n+1))
  have hr : LinearMap.range f = LinearMap.range (leadingMap q n) := by
    rw [leadingMap_range,LinearMap.range_domRestrict]
  have hk : LinearMap.ker f = (filtered q n).comap (filtered q (n+1)).subtype := by
    simp only [f,LinearMap.domRestrict,LinearMap.ker_comp,Submodule.ker_mkQ]
  have hh := f.finrank_range_add_finrank_ker
  rw [hr,hk,(Submodule.comapSubtypeEquivOfLe (filtered_mono q (Nat.le_succ n))).finrank_eq] at hh
  unfold filteredH
  rw [(leadingMap q n).quotKerEquivRange.finrank_eq]
  exact hh

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]
variable (W : (n : ℕ) → Submodule K (H (K := K) (n : ℤ)))

lemma quotientH_add_rank (n : ℕ) : quotientH W n + Module.finrank K (W n) = n+1 := by
  rw [quotientH, Submodule.finrank_quotient_add_finrank, finrank_piece]
  omega
lemma quotientH_le (n : ℕ) : quotientH W n ≤ n+1 := by
  have := quotientH_add_rank W n
  omega
variable (hW : ∀ (i : Fin 2) (n : ℕ), (W n).map (varMul i n) ≤ W (n+1))
include hW in
lemma quotientH_succ_le_of_deficit {n : ℕ}
    (hn : quotientH W n < n+1) : quotientH W (n+1) ≤ quotientH W n := by
  have h0 : W n ≠ ⊥ := by
    intro h
    have hh := quotientH_add_rank W n
    rw [h, finrank_bot] at hh
    omega
  have hh := finrank_varMul_sup (W n) h0
  have hl : Module.finrank K ↥((W n).map (varMul 0 n) ⊔ (W n).map (varMul 1 n)) ≤
      Module.finrank K (W (n+1)) := Submodule.finrank_mono (sup_le (hW 0 n) (hW 1 n))
  have h1 := quotientH_add_rank W n
  have h2 := quotientH_add_rank W (n+1)
  omega
include hW in
lemma quotientH_le_of_deficit {n m : ℕ}
    (hn : quotientH W n < n+1) (hnm : n ≤ m) : quotientH W m ≤ quotientH W n := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
    exact (quotientH_succ_le_of_deficit W hW (by omega : quotientH W m < m+1)).trans ih

theorem quotientH_coprime_bound
    {a b : Plane (K := K)} {e f : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (hb : b.IsWeightedHomogeneous weight f)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsRelPrime a b) (n : ℕ)
    (haW : multiplicationRange ha (n : ℤ) ≤ W n)
    (hbW : multiplicationRange hb (n : ℤ) ≤ W n) :
    quotientH W n + ((n : ℤ)-e+1).toNat + ((n : ℤ)-f+1).toNat ≤
      n+1 + ((n : ℤ)-(e+f)+1).toNat := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (multiplicationRange ha (n : ℤ)) (multiplicationRange hb (n : ℤ))
  rw [multiplicationRange_inf ha hb hb0 hab,
    finrank_multiplicationRange ha ha0, finrank_multiplicationRange hb hb0,
    finrank_multiplicationRange (ha.mul hb) (mul_ne_zero ha0 hb0)] at hh
  have hl : Module.finrank K ↥(multiplicationRange ha (n : ℤ) ⊔
      multiplicationRange hb (n : ℤ)) ≤ Module.finrank K (W n) :=
    Submodule.finrank_mono (sup_le haW hbW)
  have heq := quotientH_add_rank W n
  omega

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open Finset
variable (h : ℕ → ℕ)
lemma hSum_succ (n : ℕ) : hSum h (n+1) = hSum h n + h n := sum_range_succ _ _

lemma hSum_half_length (B : ℕ)
    (hle : ∀ n, h n ≤ n+1)
    (hdec : ∀ n m, h n < n+1 → n ≤ m → h m ≤ h n)
    (htail : ∀ n, B ≤ n → h n ≤ 2*B-n) :
    hSum h (2*B) ≤ 2*hSum h B := by
  have hp : ∀ i ∈ range B, h (B+i) ≤ h (B-1-i) := by
    intro i hi
    have hiB := mem_range.mp hi
    rcases (hle (B-1-i)).eq_or_lt with he|hl
    · rw [he]
      have ht := htail (B+i) (by omega)
      omega
    · exact hdec (B-1-i) (B+i) hl (by omega)
  have hs := sum_le_sum hp
  rw [sum_range_reflect] at hs
  have he : hSum h (2*B) = hSum h B + ∑ i ∈ range B, h (B+i) := by
    rw [show 2*B = B+B by omega, hSum, sum_range_add]
    rfl
  rw [he]
  dsimp only [hSum] at *
  omega

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma mul_filtered_by_homogeneous (q : Plane (K := K) →ₐ[K] R) {n m : ℕ}
    {z : R} (hz : z ∈ filtered q n) (p : H (K := K) (m : ℤ)) :
    z * q p.val ∈ filtered q (n+m) := by
  cases n with
  | zero =>
    have hz0 : z = 0 := hz
    simp [hz0]
  | succ n =>
    obtain ⟨a,ha,rfl⟩ := (mem_filtered_succ q n z).mp hz
    rw [show n+1+m = (n+m)+1 by omega]
    apply (mem_filtered_succ q (n+m) _).mpr
    refine ⟨a*p.val,?_,map_mul _ _ _⟩
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add ha (intWeight_homogeneous p.property).totalDegree_le)

lemma multiplicationRange_le_leading (q : Plane (K := K) →ₐ[K] R)
    {a : Plane (K := K)} {e : ℕ} (ha : a.IsWeightedHomogeneous weight (e : ℤ))
    (hqa : q a ∈ filtered q e) (n : ℕ) :
    multiplicationRange ha (n : ℤ) ≤ leadingRelations q n := by
  rintro _ ⟨p,rfl⟩
  rw [mem_leadingRelations]
  change q (a*p.val) ∈ _
  rw [map_mul]
  by_cases hen : e ≤ n
  · let p' : H (K := K) ((n-e : ℕ) : ℤ) := ⟨p.val, by
      have hh : (n : ℤ)-e = ((n-e : ℕ) : ℤ) := by omega
      exact hh ▸ p.property⟩
    have hh := mul_filtered_by_homogeneous q hqa p'
    simpa only [Nat.add_sub_of_le hen] using hh
  · have hr : Module.finrank K (H (K := K) ((n : ℤ)-e)) = 0 := by
      rw [finrank_piece]; omega
    obtain ⟨c,hc,hcp⟩ := Module.finrank_eq_zero_iff.mp hr p
    have hp0 : p = 0 := (smul_eq_zero.mp hcp).resolve_left hc
    rw [hp0]
    simp

lemma filtered_rank_eq_hSum (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Module.finrank K (filtered q n) = hSum (filteredH q) n := by
  induction n with
  | zero =>
    change Module.finrank K (⊥ : Submodule K R) = 0
    exact finrank_bot K R
  | succ n ih =>
    rw [hSum_succ,← ih]
    have := filteredH_add_rank q n
    omega

lemma filtered_eq_top_of_tail (q : Plane (K := K) →ₐ[K] R)
    (hq : Function.Surjective q) (N : ℕ)
    (hz : ∀ n, N ≤ n → filteredH q n = 0) : filtered q N = ⊤ := by
  have he : ∀ n, N ≤ n → filtered q n = filtered q N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have hh := filteredH_add_rank q n
      rw [hz n hn,zero_add] at hh
      exact (Submodule.eq_of_le_of_finrank_eq (filtered_mono q (Nat.le_succ n)) hh).symm.trans ih
  apply top_unique
  intro z _
  obtain ⟨p,rfl⟩ := hq z
  have hm : q p ∈ filtered q (max N (p.totalDegree+1)) :=
    filtered_mono q (le_max_right ..)
      ((mem_filtered_succ q p.totalDegree (q p)).mpr ⟨p,le_rfl,rfl⟩)
  rwa [he _ (le_max_left ..)] at hm

theorem finite_interpolation_half (q : Plane (K := K) →ₐ[K] R)
    (hq : Function.Surjective q) {a b : Plane (K := K)} {e f B : ℕ}
    (ha : a.IsWeightedHomogeneous weight (e : ℤ))
    (hb : b.IsWeightedHomogeneous weight (f : ℤ))
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsRelPrime a b)
    (hqa : q a ∈ filtered q e) (hqb : q b ∈ filtered q f)
    (he : e ≤ B+1) (hf : f ≤ B+1) (hef : e+f ≤ 2*B+1) :
    filtered q (2*B) = ⊤ ∧ Module.finrank K R ≤ 2*Module.finrank K (filtered q B) := by
  have ht : ∀ n, B ≤ n → filteredH q n ≤ 2*B-n := by
    intro n hn
    have hh := quotientH_coprime_bound (leadingRelations q) ha hb ha0 hb0 hab n
      (multiplicationRange_le_leading q ha hqa n)
      (multiplicationRange_le_leading q hb hqb n)
    change filteredH q n + _ + _ ≤ _ at hh
    omega
  have htop := filtered_eq_top_of_tail q hq (2*B) (by
    intro n hn
    have hh := ht n (by omega)
    omega)
  refine ⟨htop,?_⟩
  have hh := hSum_half_length (filteredH q) B
    (quotientH_le (leadingRelations q))
    (fun n m hn hnm => quotientH_le_of_deficit (leadingRelations q)
      (varMul_leadingRelations q) hn hnm) ht
  rw [← filtered_rank_eq_hSum, ← filtered_rank_eq_hSum, htop,finrank_top] at hh
  exact hh

end PermanentBorder.PlaneHilbert

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.HalfPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

lemma inField_lift (F : IntermediateField K L) {p : MvPolynomial (Fin 2) L}
    (hp : InField F p) : ∃ p₀ : MvPolynomial (Fin 2) F, p₀.map F.val.toRingHom = p := by
  apply mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨s,_,rfl⟩ := mem_coeffs_iff.mp hc
  exact ⟨⟨_,hp s⟩,rfl⟩

end PermanentBorder.CurveFamily

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SingularValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma pointEvaluation_apply {ι : Type*} (x : ι → Fin 2 → L)
    (p : MvPolynomial (Fin 2) L) (i : ι) : pointEvaluation x p i = eval (x i) p := by
  simp [pointEvaluation,aeval_def]

end PermanentBorder.CurveFamily

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

lemma squareForm_add (a b c d a' b' c' d' : Plane K) :
    squareForm (a+a') (b+b') (c+c') (d+d') =
      squareForm a b c d + squareForm a' b' c' d' := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp only [squareForm, add_sq, htwo, zero_mul, add_zero]
  ring

omit [CharP K 2] in
lemma squareForm_mul_zero (a b c d : Plane K) :
    squareForm a b c d * X 0 = squareForm (X 0*b) a (X 0*d) c := by
  unfold squareForm
  ring

omit [CharP K 2] in
lemma squareForm_mul_one (a b c d : Plane K) :
    squareForm a b c d * X 1 = squareForm (X 1*c) (X 1*d) a b := by
  unfold squareForm
  ring

theorem exists_squareForm [PerfectRing K 2] (f : Plane K) :
    ∃ a b c d : Plane K, f = squareForm a b c d := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      refine ⟨C ((frobeniusEquiv K 2).symm a),0,0,0,?_⟩
      simp only [squareForm, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero]
      rw [← map_pow, frobeniusEquiv_symm_pow_p]
  | add f g hf hg =>
      obtain ⟨a,b,c,d,rfl⟩ := hf
      obtain ⟨a',b',c',d',rfl⟩ := hg
      exact ⟨a+a',b+b',c+c',d+d',(squareForm_add ..).symm⟩
  | mul_X f i hf =>
      obtain ⟨a,b,c,d,rfl⟩ := hf
      fin_cases i
      · exact ⟨X 0*b,a,X 0*d,c,squareForm_mul_zero ..⟩
      · exact ⟨X 1*c,X 1*d,a,b,squareForm_mul_one ..⟩

lemma squareForm_partial_zero (a b c d : Plane K) :
    pderiv 0 (squareForm a b c d) = b^2 + X 1*d^2 := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [squareForm, htwo, mul_comm]

lemma squareForm_partial_one (a b c d : Plane K) :
    pderiv 1 (squareForm a b c d) = c^2 + X 0*d^2 := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [squareForm, htwo, mul_comm]

lemma squareForm_mixed (a b c d : Plane K) :
    pderiv 1 (pderiv 0 (squareForm a b c d)) = d^2 := by
  rw [squareForm_partial_zero]
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [htwo]

theorem wild_zero_iff (a b c d : Plane K) (p : Fin 2 → K) :
    (eval p (squareForm a b c d) = 0 ∧
      eval p (pderiv 0 (squareForm a b c d)) = 0 ∧
      eval p (pderiv 1 (squareForm a b c d)) = 0 ∧
      eval p (pderiv 1 (pderiv 0 (squareForm a b c d))) = 0) ↔
    eval p a = 0 ∧ eval p b = 0 ∧ eval p c = 0 ∧ eval p d = 0 := by
  rw [squareForm_mixed, squareForm_partial_zero, squareForm_partial_one]
  simp only [map_add, map_mul, map_pow, eval_X]
  constructor
  · rintro ⟨hf,hb,hc,hd⟩
    have hd' : eval p d = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hd
    simp only [hd', zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at hb hc
    have hb' : eval p b = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hb
    have hc' : eval p c = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hc
    have ha' : eval p a = 0 := by
      apply (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp
      simpa [squareForm,hb',hc',hd'] using hf
    exact ⟨ha',hb',hc',hd'⟩
  · rintro ⟨ha,hb,hc,hd⟩
    simp [squareForm,ha,hb,hc,hd]

end PermanentBorder.FrobeniusPlane

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

lemma wild_ideal_eq (a b c d : Plane K) :
    Ideal.span {squareForm a b c d,
      pderiv 0 (squareForm a b c d),
      pderiv 1 (squareForm a b c d),
      pderiv 1 (pderiv 0 (squareForm a b c d))} =
    Ideal.span {a^2,b^2,c^2,d^2} := by
  rw [squareForm_mixed, squareForm_partial_zero, squareForm_partial_one]
  let J : Ideal (Plane K) := Ideal.span {a^2,b^2,c^2,d^2}
  let W : Ideal (Plane K) := Ideal.span
    {squareForm a b c d,b^2+X 1*d^2,c^2+X 0*d^2,d^2}
  change W = J
  have ha : a^2 ∈ J := Ideal.subset_span (by simp)
  have hb : b^2 ∈ J := Ideal.subset_span (by simp)
  have hc : c^2 ∈ J := Ideal.subset_span (by simp)
  have hd : d^2 ∈ J := Ideal.subset_span (by simp)
  have hwd : d^2 ∈ W := Ideal.subset_span (by simp)
  have hwb : b^2 ∈ W := by
    have hh : b^2+X 1*d^2 ∈ W := Ideal.subset_span (by simp)
    exact (W.add_mem_iff_left (W.mul_mem_left _ hwd)).mp hh
  have hwc : c^2 ∈ W := by
    have hh : c^2+X 0*d^2 ∈ W := Ideal.subset_span (by simp)
    exact (W.add_mem_iff_left (W.mul_mem_left _ hwd)).mp hh
  have hwa : a^2 ∈ W := by
    have hh : squareForm a b c d ∈ W := Ideal.subset_span (by simp)
    dsimp only [squareForm] at hh
    exact (W.add_mem_iff_left (W.mul_mem_left _ hwb)).mp
      ((W.add_mem_iff_left (W.mul_mem_left _ hwc)).mp
        ((W.add_mem_iff_left (W.mul_mem_left _ hwd)).mp hh))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact J.add_mem (J.add_mem (J.add_mem ha (J.mul_mem_left _ hb))
        (J.mul_mem_left _ hc)) (J.mul_mem_left _ hd)
    · exact J.add_mem hb (J.mul_mem_left _ hd)
    · exact J.add_mem hc (J.mul_mem_left _ hd)
    · exact hd
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact hwa
    · exact hwb
    · exact hwc
    · exact hwd

end PermanentBorder.FrobeniusPlane

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.DegreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma partial_degree {f : Plane K} {n : ℕ} (hf : f.totalDegree ≤ n+1) (i : Fin 2) :
    (pderiv i f).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_pderiv] at hc
  have hp : f.coeff (m+Finsupp.single i 1) ≠ 0 := (mul_ne_zero_iff.mp hc).1
  have hd := le_totalDegree (mem_support_iff.mpr hp)
  change (m+Finsupp.single i 1).degree ≤ f.totalDegree at hd
  simp only [map_add,Finsupp.degree_single] at hd
  change m.degree ≤ n
  omega

omit [CharP K 2] in
lemma square_degree (p : Plane K) : (p^2).totalDegree = 2*p.totalDegree := by
  by_cases hp : p=0
  · simp [hp]
  · rw [pow_two,totalDegree_mul_of_isDomain hp hp]
    omega

lemma squareForm_degree_bounds {a b c d : Plane K} {n : ℕ}
    (h : (squareForm a b c d).totalDegree ≤ n+2) :
    2*a.totalDegree ≤ n+2 ∧ 2*b.totalDegree ≤ n+1 ∧
      2*c.totalDegree ≤ n+1 ∧ 2*d.totalDegree ≤ n := by
  have hx := partial_degree h 0
  have hy := partial_degree h 1
  rw [squareForm_partial_zero] at hx
  rw [squareForm_partial_one] at hy
  have hd := partial_degree (partial_degree h 0) 1
  rw [squareForm_mixed,square_degree] at hd
  have hxd : (X (0 : Fin 2)*d^2).totalDegree ≤ n+1 := by
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
  have hyd : (X (1 : Fin 2)*d^2).totalDegree ≤ n+1 := by
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
  have hb : 2*b.totalDegree ≤ n+1 := by
    rw [← square_degree]
    have he : b^2=(b^2+X 1*d^2)-X 1*d^2 := by ring
    rw [he]
    exact (totalDegree_sub _ _).trans (max_le hx hyd)
  have hc : 2*c.totalDegree ≤ n+1 := by
    rw [← square_degree]
    have he : c^2=(c^2+X 0*d^2)-X 0*d^2 := by ring
    rw [he]
    exact (totalDegree_sub _ _).trans (max_le hy hxd)
  have ha : 2*a.totalDegree ≤ n+2 := by
    rw [← square_degree]
    have he : a^2=squareForm a b c d-X 0*b^2-X 1*c^2-X 0*X 1*d^2 := by
      unfold squareForm; ring
    rw [he]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_sub _ _).trans
      apply max_le
      · apply (totalDegree_sub _ _).trans
        exact max_le h ((totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega))
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
    · have he' : X (0 : Fin 2)*X 1*d^2=X 0*(X 1*d^2) := mul_assoc ..
      rw [he']
      exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
  exact ⟨ha,hb,hc,hd⟩

omit [CharP K 2] in
lemma squareForm_degree_le {a b c d : Plane K} {n : ℕ}
    (ha : 2*a.totalDegree ≤ n) (hb : 1+2*b.totalDegree ≤ n)
    (hc : 1+2*c.totalDegree ≤ n) (hd : 2+2*d.totalDegree ≤ n) :
    (squareForm a b c d).totalDegree ≤ n := by
  unfold squareForm
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le (by simpa only [square_degree] using ha)
        ((totalDegree_mul _ _).trans (by simpa only [totalDegree_X,square_degree] using hb))
    · exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_X,square_degree] using hc)
  · have h := (totalDegree_mul (X (0 : Fin 2) : Plane K) (X 1))
    exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X,square_degree] at *; omega)

omit [CharP K 2] in
lemma subtract_top_degree {p : Plane K} {n : ℕ} (hp : p.totalDegree ≤ n+1) :
    (p-homogeneousComponent (n+1) p).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_sub,coeff_homogeneousComponent] at hc
  change m.degree ≤ n
  by_contra! hn
  by_cases he : m.degree=n+1
  · exact hc (by simp [he])
  · have hz : p.coeff m=0 := coeff_eq_zero_of_totalDegree_lt (by change p.totalDegree < m.degree; omega)
    exact hc (by simp [he,hz])

lemma squareForm_top_even {a b c d : Plane K} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r) :
    homogeneousComponent (2*r) (squareForm a b c d) =
      squareForm (homogeneousComponent r a) 0 0 (homogeneousComponent (r-1) d) := by
  let A := homogeneousComponent r a
  let D := homogeneousComponent (r-1) d
  have hdeg := squareForm_degree_bounds (n := 2*r-2) (by omega :
    (squareForm a b c d).totalDegree ≤ (2*r-2)+2)
  have ha : 2*(a-A).totalDegree ≤ 2*r-1 := by
    have hh : (a-homogeneousComponent ((r-1)+1) a).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (a-A).totalDegree ≤ r-1 at hh
    omega
  have hd : 2+2*(d-D).totalDegree ≤ 2*r-1 := by
    have hh : (d-homogeneousComponent ((r-2)+1) d).totalDegree ≤ r-2 :=
      subtract_top_degree (by omega)
    have he : r-2+1=r-1 := by omega
    rw [he] at hh
    change (d-D).totalDegree ≤ r-2 at hh
    omega
  have hlow := squareForm_degree_le ha (by omega : 1+2*b.totalDegree ≤ 2*r-1)
    (by omega : 1+2*c.totalDegree ≤ 2*r-1) hd
  have hz : homogeneousComponent (2*r) (squareForm (a-A) b c (d-D))=0 :=
    homogeneousComponent_eq_zero _ _ (by omega)
  have htop : (squareForm A 0 0 D).IsHomogeneous (2*r) := by
    simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero]
    apply IsHomogeneous.add
    · convert (homogeneousComponent_isHomogeneous r a).pow 2 using 1; omega
    · convert ((isHomogeneous_X K (0 : Fin 2)).mul (isHomogeneous_X K 1)).mul
        ((homogeneousComponent_isHomogeneous (r-1) d).pow 2) using 1; omega
  have he : squareForm a b c d = squareForm A 0 0 D + squareForm (a-A) b c (d-D) := by
    rw [← squareForm_add]
    simp only [add_sub_cancel,zero_add]
  rw [he,map_add,homogeneousComponent_eq_self htop,hz,add_zero]

lemma squareForm_top_odd {a b c d : Plane K} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1) :
    homogeneousComponent (2*r+1) (squareForm a b c d) =
      squareForm 0 (homogeneousComponent r b) (homogeneousComponent r c) 0 := by
  let B := homogeneousComponent r b
  let C' := homogeneousComponent r c
  have hdeg := squareForm_degree_bounds (n := 2*r-1) (by omega :
    (squareForm a b c d).totalDegree ≤ (2*r-1)+2)
  have hb : 1+2*(b-B).totalDegree ≤ 2*r := by
    have hh : (b-homogeneousComponent ((r-1)+1) b).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (b-B).totalDegree ≤ r-1 at hh
    omega
  have hc : 1+2*(c-C').totalDegree ≤ 2*r := by
    have hh : (c-homogeneousComponent ((r-1)+1) c).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (c-C').totalDegree ≤ r-1 at hh
    omega
  have hlow := squareForm_degree_le (by omega : 2*a.totalDegree ≤ 2*r) hb hc
    (by omega : 2+2*d.totalDegree ≤ 2*r)
  have hz : homogeneousComponent (2*r+1) (squareForm a (b-B) (c-C') d)=0 :=
    homogeneousComponent_eq_zero _ _ (by omega)
  have htop : (squareForm 0 B C' 0).IsHomogeneous (2*r+1) := by
    simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero,zero_add]
    apply IsHomogeneous.add
    · convert (isHomogeneous_X K (0 : Fin 2)).mul
        ((homogeneousComponent_isHomogeneous r b).pow 2) using 1; omega
    · convert (isHomogeneous_X K (1 : Fin 2)).mul
        ((homogeneousComponent_isHomogeneous r c).pow 2) using 1; omega
  have he : squareForm a b c d = squareForm 0 B C' 0 + squareForm a (b-B) (c-C') d := by
    rw [← squareForm_add]
    simp only [add_sub_cancel,zero_add]
  rw [he,map_add,homogeneousComponent_eq_self htop,hz,add_zero]

end PermanentBorder.FrobeniusPlane
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma homogeneous_not_unit {p : Plane K} {n : ℕ} (hp : p.IsHomogeneous n)
    (hn : 0 < n) : ¬ IsUnit p := by
  intro hu
  have hz := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have he := hp.totalDegree hu.ne_zero
  omega

omit [CharP K 2] in
lemma squarefree_even_pair {a d : Plane K}
    (h : Squarefree (squareForm a 0 0 d)) : IsRelPrime a d := by
  intro g hga hgd
  apply h g
  simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero]
  apply dvd_add
  · simpa only [pow_two] using mul_dvd_mul hga hga
  · exact dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgd hgd) _

omit [CharP K 2] in
lemma squarefree_odd_pair {b c : Plane K}
    (h : Squarefree (squareForm 0 b c 0)) : IsRelPrime b c := by
  intro g hgb hgc
  apply h g
  simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero,zero_add]
  exact dvd_add (dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgb hgb) _)
    (dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgc hgc) _)

lemma squarefree_even_leading {a b c d : Plane K} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (hs : Squarefree (homogeneousComponent (2*r) (squareForm a b c d))) :
    homogeneousComponent r a ≠ 0 ∧ homogeneousComponent (r-1) d ≠ 0 ∧
      IsRelPrime (homogeneousComponent r a) (homogeneousComponent (r-1) d) := by
  rw [squareForm_top_even hr hf] at hs
  have hp := squarefree_even_pair hs
  have ha := homogeneous_not_unit (homogeneousComponent_isHomogeneous r a) (by omega : 0 < r)
  have hd := homogeneous_not_unit (homogeneousComponent_isHomogeneous (r-1) d) (by omega : 0 < r-1)
  refine ⟨?_,?_,hp⟩
  · intro hz
    apply hd
    exact hp (by rw [hz]; exact dvd_zero _) dvd_rfl
  · intro hz
    apply ha
    exact hp dvd_rfl (by rw [hz]; exact dvd_zero _)

lemma squarefree_odd_leading {a b c d : Plane K} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (hs : Squarefree (homogeneousComponent (2*r+1) (squareForm a b c d))) :
    homogeneousComponent r b ≠ 0 ∧ homogeneousComponent r c ≠ 0 ∧
      IsRelPrime (homogeneousComponent r b) (homogeneousComponent r c) := by
  rw [squareForm_top_odd hr hf] at hs
  have hp := squarefree_odd_pair hs
  have hb := homogeneous_not_unit (homogeneousComponent_isHomogeneous r b) (by omega : 0 < r)
  have hc := homogeneous_not_unit (homogeneousComponent_isHomogeneous r c) (by omega : 0 < r)
  refine ⟨?_,?_,hp⟩
  · intro hz
    exact hc (hp (by rw [hz]; exact dvd_zero _) dvd_rfl)
  · intro hz
    exact hb (hp dvd_rfl (by rw [hz]; exact dvd_zero _))

end PermanentBorder.FrobeniusPlane

namespace PermanentBorder.BinaryLeading
open MvPolynomial
variable {K : Type*} [Field K]

lemma linear_irreducible (t : K) : Irreducible (linear t) := by
  have h := irreducible_mul_X_add (1 : MvPolynomial (Fin 2) K) (C t*X 0) 1
    one_ne_zero (by simp) (by
      intro hh
      have := vars_mul (C t : MvPolynomial (Fin 2) K) (X 0) hh
      simp at this) (isRelPrime_one_left)
  simpa only [one_mul,linear] using h

lemma linear_eval (a t : K) : eval ![1,-a] (linear t) = t-a := by
  simp [linear,sub_eq_add_neg,add_comm]

lemma linear_pair {a b : K} (hab : a ≠ b) : IsRelPrime (linear a) (linear b) := by
  apply (linear_irreducible a).isRelPrime_iff_not_dvd.mpr
  intro h
  have hh := map_dvd (eval ![1,-a]) h
  rw [linear_eval,linear_eval,sub_self,zero_dvd_iff,sub_eq_zero] at hh
  exact hab hh.symm

variable {ι : Type*} [Fintype ι]

lemma squarefree_product (t : ι → K) (ht : Function.Injective t) :
    Squarefree (∏ i, linear (t i)) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    exact linear_pair (fun h => hij (ht h))
  · intro i _
    exact (linear_irreducible (t i)).squarefree

lemma product_partial_coprime (t : ι → K) (ht : Function.Injective t) :
    IsRelPrime (∏ i, linear (t i)) (pderiv 1 (∏ i, linear (t i))) := by
  classical
  apply IsRelPrime.prod_left
  intro i hi
  apply (linear_irreducible (t i)).isRelPrime_iff_not_dvd.mpr
  intro hd
  let E := eval ![1,-t i]
  have hprod : (∏ j, linear (t j)) = linear (t i)*∏ j ∈ Finset.univ.erase i,linear (t j) :=
    (Finset.mul_prod_erase Finset.univ (fun j => linear (t j)) hi).symm
  have he : E (pderiv 1 (∏ j, linear (t j))) = ∏ j ∈ Finset.univ.erase i, (t j-t i) := by
    rw [hprod,pderiv_mul]
    have hdlin : pderiv 1 (linear (t i)) = 1 := by simp [linear]
    rw [hdlin,one_mul,map_add,map_mul]
    simp only [E,linear_eval,sub_self,zero_mul,add_zero,map_prod]
  have hh := map_dvd E hd
  rw [show E (linear (t i))=0 by simp [E,linear_eval],zero_dvd_iff,he] at hh
  obtain ⟨j,hj,hj0⟩ := Finset.prod_eq_zero_iff.mp hh
  have hji := (Finset.mem_erase.mp hj).1
  exact hji (ht (sub_eq_zero.mp hj0))

lemma product_nonzero (t : ι → K) : (∏ i, linear (t i)) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (linear_irreducible _).ne_zero

lemma product_partial_nonzero [Nonempty ι] (t : ι → K) (ht : Function.Injective t) :
    pderiv 1 (∏ i, linear (t i)) ≠ 0 := by
  intro hz
  have hunit := product_partial_coprime t ht dvd_rfl (by rw [hz]; exact dvd_zero _)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi : linear (t i) ∣ ∏ j, linear (t j) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  exact (linear_irreducible (t i)).not_isUnit (isUnit_of_dvd_unit hi hunit)

end PermanentBorder.BinaryLeading
namespace PermanentBorder.PlaneHilbert
open MvPolynomial
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma leading_vanishing_mem (q : Plane (K := K) →ₐ[K] R) {p : Plane (K := K)} {e : ℕ}
    (hp : p.totalDegree ≤ e) (hq : q p=0) : q (homogeneousComponent e p) ∈ filtered q e := by
  have hh := sub_topComponent_mem_filtered q hp
  change q p-q (homogeneousComponent e p) ∈ filtered q e at hh
  rw [hq,zero_sub] at hh
  exact (Submodule.neg_mem_iff _).mp hh

theorem finite_of_leading_pair (q : Plane (K := K) →ₐ[K] R) (hq : Function.Surjective q)
    {p t : Plane (K := K)} {e f B : ℕ} (hp : p.totalDegree ≤ e) (ht : t.totalDegree ≤ f)
    (hqp : q p=0) (hqt : q t=0) (hp0 : homogeneousComponent e p ≠ 0)
    (ht0 : homogeneousComponent f t ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e p) (homogeneousComponent f t))
    (he : e ≤ B+1) (hf : f ≤ B+1) (hef : e+f ≤ 2*B+1) :
    Module.Finite K R ∧ Module.finrank K R ≤ 2*Module.finrank K (filtered q B) := by
  have hh := finite_interpolation_half q hq
    (SliceParameters.homogeneous_intWeight (homogeneousComponent_isHomogeneous e p))
    (SliceParameters.homogeneous_intWeight (homogeneousComponent_isHomogeneous f t))
    hp0 ht0 hcop (leading_vanishing_mem q hp hqp) (leading_vanishing_mem q ht hqt) he hf hef
  refine ⟨?_,hh.2⟩
  apply Module.Finite.of_surjective (filtered q (2*B)).subtype
  intro z
  exact ⟨⟨z,by rw [hh.1]; trivial⟩,rfl⟩

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

omit [CharP L 2] in
lemma halfIdeal_mem (a b c d : Plane L) :
    a ∈ halfIdeal a b c d ∧ b ∈ halfIdeal a b c d ∧ c ∈ halfIdeal a b c d ∧ d ∈ halfIdeal a b c d := by
  exact ⟨Ideal.subset_span (by simp),Ideal.subset_span (by simp),
    Ideal.subset_span (by simp),Ideal.subset_span (by simp)⟩

lemma halfIdeal_even_finite {a b c d : Plane L} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (hs : Squarefree (homogeneousComponent (2*r) (squareForm a b c d))) :
    let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
    Module.Finite L (Plane L ⧸ halfIdeal a b c d) ∧
      finrank L (Plane L ⧸ halfIdeal a b c d) ≤ 2*finrank L (filtered q r) := by
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  have hm := halfIdeal_mem a b c d
  have hdeg := squareForm_degree_bounds (n := 2*r-2) (by simpa [show 2*r-2+2=2*r by omega] using hf)
  obtain ⟨ha0,hd0,hcop⟩ := squarefree_even_leading hr hf hs
  exact finite_of_leading_pair q Ideal.Quotient.mk_surjective
    (show a.totalDegree ≤ r by omega) (show d.totalDegree ≤ r-1 by omega)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.1) (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.2)
    ha0 hd0 hcop (by omega) (by omega) (by omega)

lemma halfIdeal_odd_finite {a b c d : Plane L} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (hs : Squarefree (homogeneousComponent (2*r+1) (squareForm a b c d))) :
    let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
    Module.Finite L (Plane L ⧸ halfIdeal a b c d) ∧
      finrank L (Plane L ⧸ halfIdeal a b c d) ≤ 2*finrank L (filtered q r) := by
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  have hm := halfIdeal_mem a b c d
  have hdeg := squareForm_degree_bounds (n := 2*r-1) (by simpa [show 2*r-1+2=2*r+1 by omega] using hf)
  obtain ⟨hb0,hc0,hcop⟩ := squarefree_odd_leading hr hf hs
  exact finite_of_leading_pair q Ideal.Quotient.mk_surjective
    (show b.totalDegree ≤ r by omega) (show c.totalDegree ≤ r by omega)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.1) (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.1)
    hb0 hc0 hcop (by omega) (by omega) (by omega)

end PermanentBorder.CurveFamily

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.WildParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
variable {L : Type*} [Field L]

lemma pointEvaluation_surjective {ι : Type*} [Fintype ι]
    (x : ι → Fin 2 → L) (hx : Function.Injective x) :
    Function.Surjective (pointEvaluation x) := by
  classical
  have hp : ∀ i j : ι, i ≠ j → ∃ p : MvPolynomial (Fin 2) L,
      eval (x i) p = 1 ∧ eval (x j) p = 0 := by
    intro i j hij
    have hne : ∃ k, x i k ≠ x j k := by
      by_contra! h
      exact hij (hx (funext h))
    obtain ⟨k,hk⟩ := hne
    refine ⟨C (x i k-x j k)⁻¹*(X k-C (x j k)),?_,?_⟩
    · simp only [map_mul,map_sub,eval_C,eval_X]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hk)
    · simp
  choose p hp using hp
  let P (i : ι) := ∏ j : {j // j ≠ i}, p i j.val (Ne.symm j.property)
  have he (i j : ι) : eval (x j) (P i) = if i=j then 1 else 0 := by
    dsimp [P]
    rw [map_prod]
    split_ifs with hij
    · subst j
      exact Finset.prod_eq_one fun z _ => (hp i z.val (Ne.symm z.property)).1
    · exact Finset.prod_eq_zero (Finset.mem_univ ⟨j,Ne.symm hij⟩)
        (hp i j hij).2
  intro y
  refine ⟨∑ i, C (y i)*P i,?_⟩
  ext j
  simp only [pointEvaluation_apply,map_sum,map_mul,eval_C,he]
  simp

lemma partial_leading (p : MvPolynomial (Fin 2) L) (n : ℕ) (i : Fin 2) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n+1) p) := by
  ext s
  simp only [coeff_homogeneousComponent,coeff_pderiv]
  have he : (s+Finsupp.single i 1).degree = s.degree+1 := by
    simp only [map_add,Finsupp.degree_single]
  rw [he]
  split_ifs <;> simp_all

end PermanentBorder.CurveFamily

namespace PermanentBorder.IdealColength
open Module
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

theorem quotient_product_length (I B : Ideal R) (z : R) :
    Module.length K (R ⧸ (I ⊔ Ideal.span {z}*B)) ≤
      Module.length K (R ⧸ (I ⊔ Ideal.span {z})) + Module.length K (R ⧸ B) := by
  let J := I ⊔ Ideal.span {z}*B
  let H := I ⊔ Ideal.span {z}
  have hJH : J ≤ H := sup_le_sup_left (Ideal.mul_le_left) I
  let g : (R ⧸ J) →ₗ[K] (R ⧸ H) := (Ideal.Quotient.factorₐ K hJH).toLinearMap
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective hJH
  let μ : R →ₗ[K] (R ⧸ J) := (Ideal.Quotient.mkₐ K J).toLinearMap.comp (LinearMap.mulLeft K z)
  have hμ : B.restrictScalars K ≤ LinearMap.ker μ := by
    intro r hr
    change Ideal.Quotient.mk J (z*r) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span {z} * B ≤ J from le_sup_right) (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hr)
  let v : (R ⧸ B) →ₗ[K] (R ⧸ J) := (B.restrictScalars K).liftQ μ hμ
  have hv : LinearMap.range v = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨a,rfl⟩
      obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
      change Ideal.Quotient.mk H (z*r) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((show Ideal.span {z} ≤ H from le_sup_right) (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))))
    · intro a ha
      obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
      have hr : r ∈ H := Ideal.Quotient.eq_zero_iff_mem.mp ha
      obtain ⟨i,hi,j,hj,he⟩ := Submodule.mem_sup.mp hr
      obtain ⟨s,hs⟩ := Ideal.mem_span_singleton'.mp hj
      refine ⟨Ideal.Quotient.mk B s,?_⟩
      change Ideal.Quotient.mk J (z*s) = Ideal.Quotient.mk J r
      rw [← he,← hs,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ J from le_sup_left) hi),zero_add]
      congr 1
      ring
  have hlen := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.subtype_injective _) hg (LinearMap.exact_subtype_ker_map g)
  have hb : Module.length K (LinearMap.ker g) ≤ Module.length K (R ⧸ B) := by
    rw [← hv]
    exact Module.length_le_of_surjective v.rangeRestrict (by
      rintro ⟨x,y,rfl⟩
      exact ⟨y,rfl⟩)
  calc
    _ = Module.length K (LinearMap.ker g) + Module.length K (R ⧸ H) := hlen
    _ ≤ Module.length K (R ⧸ B) + Module.length K (R ⧸ H) := add_le_add hb le_rfl
    _ = _ := add_comm _ _
end PermanentBorder.IdealColength
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

lemma square_mem_of_mem_span (s : Set (Plane K)) {p : Plane K}
    (hp : p ∈ Ideal.span s) : p^2 ∈ Ideal.span ((fun q : Plane K => q^2) '' s) := by
  have hs : Ideal.span s ≤ Ideal.comap (frobenius (Plane K) 2)
      (Ideal.span ((fun q : Plane K => q^2) '' s)) := by
    apply Ideal.span_le.mpr
    intro x hx
    exact Ideal.subset_span ⟨x,hx,rfl⟩
  exact hs hp

theorem frobenius_quotient_bound [PerfectRing K 2] (J H : Ideal (Plane K))
    [Module.Finite K (Plane K ⧸ J)]
    (hJ : ∀ p ∈ J, p^2 ∈ H) :
    ∃ (_ : Module.Finite K (Plane K ⧸ H)),
      Module.finrank K (Plane K ⧸ H) ≤ 4*Module.finrank K (Plane K ⧸ J) := by
  classical
  let b := Module.finBasis K (Plane K ⧸ J)
  let q := Ideal.Quotient.mkₐ K J
  let v := Ideal.Quotient.mkₐ K H
  let r : Fin (Module.finrank K (Plane K ⧸ J)) → Plane K :=
    fun i => Classical.choose (Ideal.Quotient.mk_surjective (b i))
  have hr : ∀ i, q (r i) = b i := fun i => Classical.choose_spec (Ideal.Quotient.mk_surjective (b i))
  let e : Fin 4 → Plane K := ![1,X 0,X 1,X 0*X 1]
  let u : Fin 4 × Fin (Module.finrank K (Plane K ⧸ J)) → (Plane K ⧸ H) :=
    fun i => v (e i.1 * (r i.2)^2)
  let W := Submodule.span K (Set.range u)
  have hsquare (p : Plane K) (j : Fin 4) : v (e j*p^2) ∈ W := by
    let c := b.repr (q p)
    let t : Plane K := ∑ i, c i • r i
    have ht : q t = q p := by
      simp only [t,map_sum,map_smul,hr]
      exact b.sum_repr (q p)
    have hz : p-t ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (by
      change q (p-t) = 0
      rw [map_sub,ht,sub_self])
    have hpow : v (p^2) = v (t^2) := by
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr (hJ _ hz)
      change v ((p-t)^2) = 0 at hh
      rw [sub_pow_char,map_sub] at hh
      exact sub_eq_zero.mp hh
    have hsum : v (e j*p^2) = ∑ i, (c i)^2 • u (j,i) := by
      rw [map_mul,hpow,← map_mul]
      simp only [t,sum_pow_char,Finset.mul_sum,map_sum,smul_pow,mul_smul_comm,map_smul,u]
    rw [hsum]
    exact W.sum_mem (fun i _ => W.smul_mem _ (Submodule.subset_span ⟨(j,i),rfl⟩))
  have htop : W = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a,b,c,d,rfl⟩ := exists_squareForm p
    change v (squareForm a b c d) ∈ W
    simp only [squareForm,map_add]
    exact W.add_mem (W.add_mem (W.add_mem (by simpa [e] using hsquare a 0)
      (by simpa [e] using hsquare b 1)) (by simpa [e] using hsquare c 2))
      (by simpa [e] using hsquare d 3)
  have hfg : (⊤ : Submodule K (Plane K ⧸ H)).FG := by
    rw [← htop]
    exact Submodule.fg_span (Set.finite_range u)
  let hfinite : Module.Finite K (Plane K ⧸ H) := Module.Finite.of_fg_top hfg
  refine ⟨hfinite,?_⟩
  simpa using finrank_le_of_span_eq_top htop
end PermanentBorder.FrobeniusPlane
namespace PermanentBorder.CurveFamily
open MvPolynomial Module
variable {K : Type*} [Field K]

lemma zeroEvaluation_surjective (I : Ideal (MvPolynomial (Fin 2) K))
    [Fintype (zeroLocus K I)] : Function.Surjective (zeroEvaluation I) := by
  intro z
  obtain ⟨p,hp⟩ := pointEvaluation_surjective (fun x : zeroLocus K I => x.val)
    Subtype.val_injective z
  exact ⟨Ideal.Quotient.mk I p,hp⟩

lemma finite_zeroLocus (I : Ideal (MvPolynomial (Fin 2) K))
    [Module.Finite K (MvPolynomial (Fin 2) K ⧸ I)] : Finite (zeroLocus K I) := by
  let v : zeroLocus K I → ((MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] K) := fun x =>
    Ideal.Quotient.liftₐ I (aeval x.val) (mem_zeroLocus_iff.mp x.property)
  apply Finite.of_injective v
  intro x y hxy
  apply Subtype.ext
  funext i
  have h := congrArg (fun g : (MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] K =>
    g (Ideal.Quotient.mk I (X i))) hxy
  simpa [v] using h

lemma zero_card_le_finrank (I : Ideal (MvPolynomial (Fin 2) K))
    [Module.Finite K (MvPolynomial (Fin 2) K ⧸ I)] [Fintype (zeroLocus K I)] :
    Fintype.card (zeroLocus K I) ≤ finrank K (MvPolynomial (Fin 2) K ⧸ I) := by
  simpa only [Module.finrank_pi, finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul,mul_one] using
    LinearMap.finrank_le_finrank_of_surjective (f := (zeroEvaluation I).toLinearMap)
      (zeroEvaluation_surjective I)

lemma radical_length_eq_zero_card [IsAlgClosed K] (I : Ideal (MvPolynomial (Fin 2) K))
    [Fintype (zeroLocus K I)] :
    Module.length K (MvPolynomial (Fin 2) K ⧸ I.radical) = Fintype.card (zeroLocus K I) := by
  let g : MvPolynomial (Fin 2) K →ₐ[K] (zeroLocus K I → K) :=
    pointEvaluation (fun x : zeroLocus K I => x.val)
  have hg : Function.Surjective g := pointEvaluation_surjective _ Subtype.val_injective
  have hker : RingHom.ker g = I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K) I]
    ext p
    simp only [RingHom.mem_ker]
    constructor
    · intro hp x hx
      have hh := congrFun hp ⟨x,hx⟩
      exact hh
    · intro hp
      ext x
      exact hp x.val x.property
  let e := Ideal.quotientEquivAlgOfEq K hker.symm
  let e' := Ideal.quotientKerAlgEquivOfSurjective hg
  rw [(e.trans e').toLinearEquiv.length_eq]
  simp [Module.length_eq_finrank]

end PermanentBorder.CurveFamily

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConductorDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.CurveFamily
open MvPolynomial Module FrobeniusPlane
open scoped Classical
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma singular_zero_iff (f : Plane K) (x : Fin 2 → K) :
    x ∈ zeroLocus K (singularIdeal f) ↔
      eval x f=0 ∧ eval x (pderiv 0 f)=0 ∧ eval x (pderiv 1 f)=0 := by
  change singularIdeal f ≤ RingHom.ker (aeval x) ↔ _
  rw [singularIdeal,Ideal.span_le]
  simp only [Set.insert_subset_iff,Set.singleton_subset_iff]
  rfl

lemma singular_add_square_eq (a b c d : Plane K) :
    singularIdeal (squareForm a b c d) ⊔ Ideal.span {d^2} = Ideal.span {a^2,b^2,c^2,d^2} := by
  rw [← wild_ideal_eq, squareForm_mixed,singularIdeal,← Ideal.span_union]
  congr 1
  ext p
  simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
  tauto

lemma singular_wild_card_le (a b c d : Plane K)
    [Fintype (zeroLocus K (singularIdeal (squareForm a b c d)))]
    [Module.Finite K (Plane K ⧸ halfIdeal a b c d)] :
    Fintype.card {x : zeroLocus K (singularIdeal (squareForm a b c d)) // eval x.val d=0} ≤
      finrank K (Plane K ⧸ halfIdeal a b c d) := by
  classical
  let := finite_zeroLocus (halfIdeal a b c d)
  let := Fintype.ofFinite (zeroLocus K (halfIdeal a b c d))
  let v : {x : zeroLocus K (singularIdeal (squareForm a b c d)) // eval x.val d=0} →
      zeroLocus K (halfIdeal a b c d) := fun x => ⟨x.val.val,by
    have h := (singular_zero_iff _ _).mp x.val.property
    have h' := (wild_zero_iff a b c d x.val.val).mp
      ⟨h.1,h.2.1,h.2.2,by rw [squareForm_mixed,map_pow,x.property]; simp⟩
    change halfIdeal a b c d ≤ RingHom.ker (aeval x.val.val)
    rw [halfIdeal,Ideal.span_le]
    simp only [Set.insert_subset_iff,Set.singleton_subset_iff]
    exact h'⟩
  have hv : Function.Injective v := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : zeroLocus K (halfIdeal a b c d) => z.val) hxy
  exact (Fintype.card_le_of_injective v hv).trans (zero_card_le_finrank _)

lemma singular_point_card_le (a b c d : Plane K)
    [Fintype (zeroLocus K (singularIdeal (squareForm a b c d)))]
    [Module.Finite K (Plane K ⧸ halfIdeal a b c d)] :
    Fintype.card (zeroLocus K (singularIdeal (squareForm a b c d))) ≤
      finrank K (Plane K ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus K (singularIdeal (squareForm a b c d)) // eval x.val d≠0} := by
  classical
  have h := singular_wild_card_le a b c d
  have he := Fintype.card_congr (Equiv.sumCompl
    (fun x : zeroLocus K (singularIdeal (squareForm a b c d)) => eval x.val d=0))
  rw [Fintype.card_sum] at he
  simp only [ne_eq] at *
  omega

theorem singular_enlarged_length [IsAlgClosed K] [PerfectRing K 2]
    (a b c d : Plane K)
    [Fintype (zeroLocus K (singularIdeal (squareForm a b c d)))]
    [Module.Finite K (Plane K ⧸ halfIdeal a b c d)] :
    let I := singularIdeal (squareForm a b c d)
    Module.length K (Plane K ⧸ (I ⊔ Ideal.span {d^2}*I.radical)) ≤
      (5*finrank K (Plane K ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus K I // eval x.val d≠0} : ℕ) := by
  intro I
  have hF := frobenius_quotient_bound (halfIdeal a b c d) (I ⊔ Ideal.span {d^2}) (by
    intro p hp
    rw [singular_add_square_eq]
    simpa only [Set.image_insert_eq,Set.image_singleton] using
      square_mem_of_mem_span {a,b,c,d} hp)
  obtain ⟨hfinite,hbound⟩ := hF
  let := hfinite
  have hrad := radical_length_eq_zero_card I
  have hpoint := singular_point_card_le a b c d
  calc
    _ ≤ Module.length K (Plane K ⧸ (I ⊔ Ideal.span {d^2})) +
        Module.length K (Plane K ⧸ I.radical) :=
      IdealColength.quotient_product_length I I.radical (d^2)
    _ = (finrank K (Plane K ⧸ (I ⊔ Ideal.span {d^2})) +
        Fintype.card (zeroLocus K I) : ℕ) := by rw [Module.length_eq_finrank,hrad]; simp
    _ ≤ _ := by exact_mod_cast (show finrank K (Plane K ⧸ (I ⊔ Ideal.span {d^2})) +
        Fintype.card (zeroLocus K I) ≤ _ by
          dsimp [I] at *
          omega)

end PermanentBorder.CurveFamily

namespace PermanentBorder.PlaneBivariate
open Polynomial MvPolynomial
variable (K : Type*) [Field K]

lemma derivative_to (p : MvPolynomial (Fin 2) K) :
    Polynomial.derivative (toBivariate K p) = toBivariate K (pderiv 1 p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,Polynomial.derivative_mul,pderiv_mul,map_add,map_mul]
    fin_cases i <;> simp [hp]

lemma map_to {L : Type*} [Field L] [Algebra K L] (p : MvPolynomial (Fin 2) K) :
    toBivariate L (p.map (algebraMap K L)) =
      (toBivariate K p).map (Polynomial.mapRingHom (algebraMap K L)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.map_mul,MvPolynomial.map_X,hp]
    fin_cases i <;> simp

end PermanentBorder.PlaneBivariate

namespace PermanentBorder.PlaneScaling
open Polynomial MvPolynomial
variable {K σ : Type*} [Field K]

lemma scale_monomial (s : σ →₀ ℕ) (c : K) :
    scale (MvPolynomial.monomial s c) =
      Polynomial.monomial s.degree (MvPolynomial.monomial s c) := by
  classical
  simp only [scale,MvPolynomial.aeval_def,MvPolynomial.eval₂_monomial,
    mul_pow,Finsupp.prod,Finset.prod_mul_distrib,← map_pow,← map_prod,
    Finset.prod_pow_eq_pow_sum,← Polynomial.C_mul_X_pow_eq_monomial]
  change Polynomial.C (MvPolynomial.C c) * (Polynomial.C _ * Polynomial.X ^ s.degree) = _
  rw [← mul_assoc,← map_mul]
  simp only [MvPolynomial.monomial_eq,Finsupp.prod]

lemma coeff_scale (p : MvPolynomial σ K) (n : ℕ) :
    (scale p).coeff n = homogeneousComponent n p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [scale_monomial,Polynomial.coeff_monomial]
    ext t
    simp only [coeff_homogeneousComponent,apply_ite,MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_zero]
    split_ifs <;> simp_all <;> (rintro rfl; contradiction)
  | add p q hp hq => simp only [map_add,Polynomial.coeff_add,hp,hq]

lemma degree_le_of_scale (p : MvPolynomial σ K) (n : ℕ)
    (h : (scale p).natDegree ≤ n) : p.totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro s hs
  change s.degree ≤ n
  by_contra hn
  have hz : homogeneousComponent s.degree p=0 := by
    rw [← coeff_scale]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have he := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff s) hz
  simp only [coeff_homogeneousComponent,ite_true,AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at he
  exact (MvPolynomial.mem_support_iff.mp hs) he

end PermanentBorder.PlaneScaling

namespace PermanentBorder.Conductor
open Polynomial Module
variable {K S : Type*} [Field K] [CommRing S] [IsDomain S]
  [IsPrincipalIdealRing S] [Algebra K S]

theorem normalization_length_le_ideal (f : S[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap S (FractionRing S))).Separable) (J : Ideal S[X])
    (hJ : ∀ z ∈ J, ∀ t : AdjoinRoot (f.map (algebraMap S (FractionRing S))), IsIntegral S t →
      ∃ q : S[X], AdjoinRoot.mk _ (q.map (algebraMap S (FractionRing S))) =
        AdjoinRoot.mk _ (z.map (algebraMap S (FractionRing S)))*t) :
    let R := integralClosure S (AdjoinRoot (f.map (algebraMap S (FractionRing S))))
    Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := FractionRing S) f hf).toLinearMap) ≤ Module.length K (S[X] ⧸ J) := by
  let R := integralClosure S (AdjoinRoot (f.map (algebraMap S (FractionRing S))))
  let := (normalizationInclusion (Q := FractionRing S) f hf).toRingHom.toAlgebra
  let c := (algebraConductor (AdjoinRoot f) R).restrictScalars S
  let g : S[X] →ₗ[K] (AdjoinRoot f ⧸ c) :=
    (c.mkQ.restrictScalars K).comp ((AdjoinRoot.mkₐ f).toLinearMap.restrictScalars K)
  have hg : Function.Surjective g := c.mkQ_surjective.comp AdjoinRoot.mk_surjective
  have hker : J.restrictScalars K ≤ g.ker := by
    intro z hz
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change AdjoinRoot.mk f z ∈ algebraConductor (AdjoinRoot f) R
    intro t
    obtain ⟨q,hq⟩ := hJ z hz t.val t.property
    refine ⟨AdjoinRoot.mk f q,?_⟩
    apply Subtype.ext
    change genericBaseChange (Q := FractionRing S) f (AdjoinRoot.mk f q) =
      genericBaseChange (Q := FractionRing S) f (AdjoinRoot.mk f z)*t.val
    simpa only [genericBaseChange_mk] using hq
  let v := (J.restrictScalars K).liftQ g hker
  have hv : Function.Surjective v := by
    intro y
    obtain ⟨z,hz⟩ := hg y
    exact ⟨Ideal.Quotient.mk J z,hz⟩
  obtain ⟨e⟩ := exists_normalization_conductor_cokernel_equiv hf hsep
  calc
    _ = Module.length K (AdjoinRoot f ⧸ c) := (e.restrictScalars K).length_eq.symm
    _ ≤ Module.length K (S[X] ⧸ J) := Module.length_le_of_surjective v hv

theorem normalization_length_le_enlarged [CharP S 2]
    (δ : Derivation K S S) (x : S) (hx : δ x = 1)
    (hres : ∀ (P : Ideal S) [P.IsMaximal], IsAlgClosed P.ResidueField)
    (f a b c d : S[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap S (FractionRing S))).Separable)
    (hsq : f=a^2+C x*b^2+X*c^2+C x*X*d^2)
    (hder : f.derivative=c^2+C x*d^2) :
    let R := integralClosure S (AdjoinRoot (f.map (algebraMap S (FractionRing S))))
    Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := FractionRing S) f hf).toLinearMap) ≤
      Module.length K (S[X] ⧸ ReducedBranchConductor.enlargedGradientIdeal f b c d x) := by
  apply normalization_length_le_ideal f hf hsep
  intro z hz t ht
  exact ReducedBranchConductor.reduced_global_realization δ x hx hres f a b c d hf hsep
    hsq hder z hz t ht

end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial MvPolynomial Module
open FrobeniusPlane CurveFamily PlaneBivariate
open scoped Classical
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma equiv_ring_apply (p : Plane K) : (equiv K).toRingHom p = toBivariate K p := rfl

lemma map_singularIdeal (a b c d : Plane K) :
    (singularIdeal (squareForm a b c d)).map (equiv K).toRingHom =
      ReducedBranchConductor.gradientIdeal (toBivariate K (squareForm a b c d))
        (toBivariate K b) (toBivariate K c) (toBivariate K d) Polynomial.X := by
  rw [singularIdeal,Ideal.map_span]
  simp only [squareForm_partial_zero,squareForm_partial_one,
    Set.image_insert_eq,Set.image_singleton,equiv_ring_apply,map_add,map_mul,map_pow,to_zero,to_one,
    ReducedBranchConductor.gradientIdeal]

lemma map_enlargedIdeal (a b c d : Plane K) :
    (singularIdeal (squareForm a b c d) ⊔ Ideal.span {d^2}*
      (singularIdeal (squareForm a b c d)).radical).map (equiv K).toRingHom =
      ReducedBranchConductor.enlargedGradientIdeal (toBivariate K (squareForm a b c d))
        (toBivariate K b) (toBivariate K c) (toBivariate K d) Polynomial.X := by
  rw [Ideal.map_sup,Ideal.map_mul,Ideal.map_radical_of_surjective
      (show Function.Surjective (equiv K).toRingHom from (equiv K).surjective)
      (by rw [(RingHom.injective_iff_ker_eq_bot (equiv K).toRingHom).mp (equiv K).injective]; exact bot_le),
    map_singularIdeal,ReducedBranchConductor.enlargedGradientIdeal,Ideal.map_span]
  simp only [Set.image_singleton,map_pow,equiv_ring_apply]

theorem normalization_length_le_half [IsAlgClosed K] [PerfectRing K 2]
    (a b c d : Plane K)
    (hf : (toBivariate K (squareForm a b c d)).Monic)
    (hsep : ((toBivariate K (squareForm a b c d)).map
      (algebraMap K[X] (FractionRing K[X]))).Separable)
    [Fintype (zeroLocus K (singularIdeal (squareForm a b c d)))]
    [Module.Finite K (Plane K ⧸ halfIdeal a b c d)] :
    let f := toBivariate K (squareForm a b c d)
    let R := integralClosure K[X] (AdjoinRoot (f.map (algebraMap K[X] (FractionRing K[X]))))
    Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := FractionRing K[X]) f hf).toLinearMap) ≤
      (5*finrank K (Plane K ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus K (singularIdeal (squareForm a b c d)) // eval x.val d≠0} : ℕ) := by
  let f := toBivariate K (squareForm a b c d)
  let I := singularIdeal (squareForm a b c d)
  let J := I ⊔ Ideal.span {d^2}*I.radical
  let e := Ideal.quotientEquivAlg (R₁ := K) J
    (ReducedBranchConductor.enlargedGradientIdeal f (toBivariate K b) (toBivariate K c)
      (toBivariate K d) Polynomial.X) (equiv K) (map_enlargedIdeal a b c d).symm
  have hu := normalization_length_le_enlarged (Polynomial.derivative' : Derivation K K[X] K[X]) Polynomial.X
    (by simp) (ReducedBranchConductor.polynomial_residue_algClosed (K := K))
    f (toBivariate K a) (toBivariate K b) (toBivariate K c) (toBivariate K d) hf hsep
    (by simp [f,squareForm]) (by
      rw [derivative_to,squareForm_partial_one]
      simp)
  exact hu.trans (e.toLinearEquiv.length_eq.symm.le.trans (singular_enlarged_length a b c d))

end PermanentBorder.Conductor

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma singular_finite (f : Plane L) {k : ℕ} (hk : 1 ≤ k)
    (hf : f.totalDegree ≤ k) (hlead : homogeneousComponent k f ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k f) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k f) (pderiv 1 (homogeneousComponent k f))) :
    Module.Finite L (Plane L ⧸ singularIdeal f) := by
  let q := Ideal.Quotient.mkₐ L (singularIdeal f)
  have he : homogeneousComponent (k-1) (pderiv 1 f)=pderiv 1 (homogeneousComponent k f) := by
    simpa only [Nat.sub_add_cancel hk] using partial_leading f (k-1) 1
  have hfq : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hdq : q (pderiv 1 f) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hdeg : (pderiv 1 f).totalDegree ≤ k-1 :=
    partial_degree (by rwa [Nat.sub_add_cancel hk]) 1
  exact (finite_of_leading_pair q Ideal.Quotient.mk_surjective hf hdeg hfq hdq hlead
    (by rwa [he]) (by rwa [he]) (B := k-1) (by omega) (by omega) (by omega)).1

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

lemma halfIdeal_finite {a b c d : Plane L} {k : ℕ} (hk : 4 ≤ k)
    (hf : (squareForm a b c d).totalDegree ≤ k)
    (hs : Squarefree (homogeneousComponent k (squareForm a b c d))) :
    Module.Finite L (Plane L ⧸ halfIdeal a b c d) := by
  have hrep : ∃ r, k=2*r ∨ k=2*r+1 := ⟨k/2,by omega⟩
  obtain ⟨r,h|h⟩ := hrep
  · subst k
    exact (halfIdeal_even_finite (by omega) hf hs).1
  · subst k
    exact (halfIdeal_odd_finite (by omega) hf hs).1

end PermanentBorder.CurveFamily

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SpectralPlane
open Polynomial MvPolynomial Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

lemma scale_C (c : K) : PlaneScaling.scale (MvPolynomial.C c : MvPolynomial (Fin 2) K) =
    Polynomial.C (MvPolynomial.C c) := by
  simp only [PlaneScaling.scale,MvPolynomial.aeval_C]
  rfl

lemma scale_linear (t : K) : PlaneScaling.scale (BinaryLeading.linear t) =
    Polynomial.C (BinaryLeading.linear t)*Polynomial.X := by
  simp [PlaneScaling.scale,BinaryLeading.linear]
  ring

omit [Fintype ι] in
lemma scale_matrix (θ : ι → K) (A : Matrix ι ι K) :
    (matrix θ A).map PlaneScaling.scale =
      (Polynomial.X : (MvPolynomial (Fin 2) K)[X]) • (slope θ).map Polynomial.C +
        (A.map MvPolynomial.C).map Polynomial.C := by
  apply Matrix.ext
  intro i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.map_apply,matrix,slope,Matrix.add_apply,
      Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,map_add,scale_linear,scale_C]
    change Polynomial.C (BinaryLeading.linear (θ i))*Polynomial.X +
      Polynomial.C (MvPolynomial.C (A i i)) =
      Polynomial.X*Polynomial.C (BinaryLeading.linear (θ i)) +
        Polynomial.C (MvPolynomial.C (A i i))
    rw [mul_comm (Polynomial.C _) Polynomial.X]
  · simp only [Matrix.map_apply,matrix,slope,Matrix.add_apply,
      Matrix.diagonal_apply_ne _ h,Matrix.smul_apply,smul_eq_mul,map_zero,zero_add,mul_zero]
    exact scale_C _

lemma totalDegree_equation (θ : ι → K) (A : Matrix ι ι K) :
    (equation θ A).totalDegree ≤ Fintype.card ι := by
  apply PlaneScaling.degree_le_of_scale
  have hmap := RingHom.map_det PlaneScaling.scale.toRingHom (matrix θ A)
  change PlaneScaling.scale (equation θ A) = ((matrix θ A).map PlaneScaling.scale).det at hmap
  rw [hmap,scale_matrix]
  exact Polynomial.natDegree_det_X_add_C_le _ _

lemma leading_equation (θ : ι → K) (A : Matrix ι ι K) :
    homogeneousComponent (Fintype.card ι) (equation θ A) = ∏ i, BinaryLeading.linear (θ i) := by
  have hmap := RingHom.map_det PlaneScaling.scale.toRingHom (matrix θ A)
  change PlaneScaling.scale (equation θ A) = ((matrix θ A).map PlaneScaling.scale).det at hmap
  rw [← PlaneScaling.coeff_scale,hmap,scale_matrix,Polynomial.coeff_det_X_add_C_card]
  exact Matrix.det_diagonal

lemma to_charpoly (θ : ι → K) (A : Matrix ι ι K) :
    PlaneBivariate.toBivariate K (equation θ A) =
      (-((Polynomial.X : K[X]) • (Matrix.diagonal θ).map Polynomial.C +
        A.map Polynomial.C)).charpoly := by
  have hmap := RingHom.map_det (PlaneBivariate.toBivariate K).toRingHom (matrix θ A)
  change PlaneBivariate.toBivariate K (equation θ A) =
    ((matrix θ A).map (PlaneBivariate.toBivariate K)).det at hmap
  rw [hmap,Matrix.charpoly]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases h : i=j
  · subst j
    simp [matrix,slope,BinaryLeading.linear,Matrix.charmatrix]
    ring
  · simp [matrix,slope,BinaryLeading.linear,Matrix.charmatrix,h]

omit [DecidableEq ι] in
lemma homogeneous_leading (θ : ι → K) :
    (∏ i, BinaryLeading.linear (θ i)).IsHomogeneous (Fintype.card ι) := by
  classical
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => BinaryLeading.linear (θ i))
      (fun _ : ι => 1) (fun i _ => (isHomogeneous_X K 1).add
        ((isHomogeneous_X K 0).C_mul (θ i)))

omit [DecidableEq ι] in
lemma map_leading {L : Type*} [Field L] [Algebra K L] (θ : ι → K) :
    (∏ i, BinaryLeading.linear (θ i)).map (algebraMap K L) =
      ∏ i, BinaryLeading.linear (algebraMap K L (θ i)) := by
  simp [BinaryLeading.linear]

end PermanentBorder.SpectralPlane

namespace PermanentBorder.SpectralDimension
open MvPolynomial Polynomial Matrix
open Conductor AdjugateAlgebra DeterminantFibers SpectralPlane FrobeniusPlane CurveFamily
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma curveField_le_of_inField (E : IntermediateField K L) (f : Plane L)
    (hf : CurveFamily.InField E f) :
    curveCoefficientField (K := K) (PlaneBivariate.toBivariate L f) ≤ E := by
  obtain ⟨f₀,hf₀⟩ := CurveFamily.inField_lift E hf
  have hb : Bivariate.InField E (PlaneBivariate.toBivariate L f) := by
    apply (Bivariate.inField_iff_lifts E _).mpr
    refine ⟨PlaneBivariate.toBivariate E f₀,?_⟩
    rw [← hf₀]
    change (PlaneBivariate.toBivariate E f₀).map (Polynomial.mapRingHom (algebraMap E L)) =
      PlaneBivariate.toBivariate L (MvPolynomial.map (algebraMap E L) f₀)
    exact (PlaneBivariate.map_to E f₀).symm
  apply IntermediateField.adjoin_le_iff.mpr
  rintro c ⟨⟨i,j⟩,rfl⟩
  exact hb i j

lemma to_pencil_det {k : ℕ} (θ : Fin (k+1) → L)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) :
    PlaneBivariate.toBivariate L (SpectralPlane.equation θ A) =
      (pencilMatrix (pencilBase θ A)).det := by
  rw [SpectralPlane.to_charpoly,Matrix.charpoly]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : i=j <;> simp [Matrix.charmatrix,pencilMatrix,pencilBase,Matrix.scalar_apply,hij]
  ring

variable [CharP K 2] [CharP L 2] [PerfectRing K 2] [Infinite K] [IsAlgClosed L]

theorem spectral_effective_bound_oai {k : ℕ} (hk : 4 ≤ k+1)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (T : ℕ)
    (hT : (T : ℕ∞) ≤ normalizationDefect (fun i => algebraMap K L (θ i)) A) :
    ∃ n : ℕ, Algebra.trdeg K (curveCoefficientField (K := K)
      (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det) ≤ (n : Cardinal) ∧
      18*n+T ≤ 9*((k+1)*(k+2)) := by
  let θL : Fin (k+1) → L := fun i => algebraMap K L (θ i)
  have hθL : Function.Injective θL := (algebraMap K L).injective.comp hθ
  let f := SpectralPlane.equation θL A
  obtain ⟨a,b,c,d,he⟩ := exists_squareForm f
  have hdeg : (squareForm a b c d).totalDegree ≤ k+1 := by
    rw [← he]
    simpa only [f,Fintype.card_fin] using SpectralPlane.totalDegree_equation θL A
  have hlead : homogeneousComponent (k+1) (squareForm a b c d) =
      ∏ i, BinaryLeading.linear (θL i) := by
    rw [← he]
    simpa only [f,Fintype.card_fin] using SpectralPlane.leading_equation θL A
  have hsf := BinaryLeading.squarefree_product θL hθL
  have hnz := BinaryLeading.product_nonzero θL
  have hpz := BinaryLeading.product_partial_nonzero θL hθL
  have hcop := BinaryLeading.product_partial_coprime θL hθL
  have hs' : Squarefree (homogeneousComponent (k+1) (squareForm a b c d)) := hlead.symm ▸ hsf
  have hn' : homogeneousComponent (k+1) (squareForm a b c d) ≠ 0 := hlead.symm ▸ hnz
  have hp' : pderiv 1 (homogeneousComponent (k+1) (squareForm a b c d)) ≠ 0 := hlead.symm ▸ hpz
  have hc' : IsRelPrime (homogeneousComponent (k+1) (squareForm a b c d))
      (pderiv 1 (homogeneousComponent (k+1) (squareForm a b c d))) := hlead.symm ▸ hcop
  let := CurveFamily.singular_finite (squareForm a b c d) (by omega) hdeg hn' hp' hc'
  let := CurveFamily.finite_zeroLocus (singularIdeal (squareForm a b c d))
  let := Fintype.ofFinite (zeroLocus L (singularIdeal (squareForm a b c d)))
  let := CurveFamily.halfIdeal_finite hk hdeg hs'
  obtain ⟨E,n,hE,htr,hnum⟩ := CurveFamily.half_curve_parameter_bound hk hdeg hs' hn' hp' hc'
    (∏ i, BinaryLeading.linear (θ i)) (by simpa only [Fintype.card_fin] using SpectralPlane.homogeneous_leading θ)
    (hlead.trans (SpectralPlane.map_leading θ).symm)
  have hmon : (PlaneBivariate.toBivariate L (squareForm a b c d)).Monic := by
    rw [← he,SpectralPlane.to_charpoly]
    exact Matrix.charpoly_monic _
  have hsep : ((PlaneBivariate.toBivariate L (squareForm a b c d)).map
      (algebraMap L[X] (FractionRing L[X]))).Separable := by
    rw [← he,SpectralPlane.to_charpoly]
    exact PencilSeparability.distinct_slope_pencil_separable θL hθL A
  have hnorm := Conductor.normalization_length_le_half a b c d hmon hsep
  have hnorm' : normalizationDefect θL A ≤
      (5*Module.finrank L (Plane L ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} : ℕ) := by
    let D (p : L[X][X]) (hp : p.Monic) : ℕ∞ :=
      let R := integralClosure L[X] (AdjoinRoot (p.map (algebraMap L[X] (FractionRing L[X]))))
      Module.length L (R ⧸ LinearMap.range
        (normalizationInclusion (Q := FractionRing L[X]) p hp).toLinearMap)
    have hD (p q : L[X][X]) (hp : p.Monic) (hq : q.Monic) (heq : p=q) :
        D p hp = D q hq := by subst q; rfl
    have hp : PlaneBivariate.toBivariate L (squareForm a b c d) =
        (-pencilBase θL A).charpoly := by rw [← he,SpectralPlane.to_charpoly]; rfl
    change D _ hmon ≤ _ at hnorm
    change D _ (Matrix.charpoly_monic _) ≤ _
    rw [← hD _ _ hmon (Matrix.charpoly_monic _) hp]
    exact hnorm
  have hTN : T ≤ 5*Module.finrank L (Plane L ⧸ halfIdeal a b c d) +
      Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} := by
    exact_mod_cast hT.trans hnorm'
  simp only [Nat.add_assoc,Nat.reduceAdd] at hnum
  refine ⟨n,?_,by omega⟩
  have hfE : CurveFamily.InField E f := he.symm ▸ hE
  have hle := curveField_le_of_inField E f hfE
  rw [to_pencil_det] at hle
  exact (trdeg_le_of_injective (IntermediateField.inclusion hle) (IntermediateField.inclusion_injective hle)).trans htr

end PermanentBorder.SpectralDimension

end OAI
end

theorem solution.{u} : type_of% @OAI.PermanentBorder.SpectralDimension.spectral_effective_bound_oai.{u} := @OAI.PermanentBorder.SpectralDimension.spectral_effective_bound_oai.{u}
