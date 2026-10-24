-- Prove2me | solution 1 for OAI.PermanentBorder.exists_effective_critical_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T20:03:01.977018+00:00
-- url     : https://prove2.me/submissions/6af70c82-b27d-45c7-872e-8976bde73b1f

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_OAIQWPB000
import Theorems.Thm_OAI_PermanentBorder_SpectralDimension_spectral_effective_bound

section
-- module Solutions.OAIQW_PermanentBorder.HomogeneousPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial

lemma diagonalCoefficient_map {I R S : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (M : Matrix I I R) (θ : I → R) (q : ℕ) :
    φ (diagonalCoefficient M θ q) =
      diagonalCoefficient (fun i j => φ (M i j)) (fun i => φ (θ i)) q := by
  classical
  unfold diagonalCoefficient
  rw [← coeff_map]
  apply congrArg (fun polynomial : MvPolynomial (Fin 2) S => polynomial.coeff (countIndex q))
  unfold Matrix.permanent
  simp only [map_sum,map_prod]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.prod_congr rfl
  intro i _
  simp only [Matrix.add_apply, Matrix.of_apply,Matrix.diagonal_apply,map_add,map_C]
  split_ifs <;> simp

end PermanentBorder.Selector

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Transcendence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.ParameterBounds
open Algebra MvPolynomial
universe u
variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]

theorem trdeg_lt_of_relation {n : ℕ} (x : Fin n → A)
    [Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A]
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hx : aeval x p = 0) :
    Algebra.trdeg K A < (n : Cardinal) := by
  by_contra! ht
  have ht' : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤
      Cardinal.lift.{0} (Algebra.trdeg K A) := by simpa using ht
  have hi := (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K x ht').1
  apply hp
  exact hi (by simpa using hx)

theorem adjoin_trdeg_lt_of_relation {n : ℕ} (x : Fin n → A)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hx : aeval x p = 0) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range x)) < (n : Cardinal) := by
  let B := Algebra.adjoin K (Set.range x)
  let y : Fin n → B := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have htop : Algebra.adjoin K (Set.range y) = ⊤ := by
    apply Subalgebra.map_injective (show Function.Injective B.val from Subtype.val_injective)
    rw [AlgHom.map_adjoin, Algebra.map_top, B.range_val, ← Set.range_comp]
    rfl
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range y)) B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin K (Set.range y) := by rw [htop]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin K (Set.range y)) ⟨b, hb⟩
  apply trdeg_lt_of_relation y p hp
  apply (show Function.Injective B.val from Subtype.val_injective)
  rw [map_zero, MvPolynomial.comp_aeval_apply]
  exact hx

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_lt_of_relation {L : Type u} [Field L] [Algebra K L]
    {n : ℕ} (x : Fin n → L) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) < (n : Cardinal) := by
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact adjoin_trdeg_lt_of_relation x p hp hx

end PermanentBorder.ParameterBounds

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
open Polynomial Matrix Module
section Eigenbasis
variable {Q L ι : Type*} [Field Q] [Field L] [Algebra Q L]
  [Fintype ι] [DecidableEq ι]

theorem exists_splitting_eigenbasis (T : Matrix ι ι Q)
    (hsep : T.charpoly.Separable)
    (hsplit : (T.charpoly.map (algebraMap Q L)).Splits) :
    ∃ b : Basis (T.charpoly.rootSet L) L (ι → L),
      ∀ μ, (T.map (algebraMap Q L)) *ᵥ b μ = μ.val • b μ := by
  classical
  let U := T.map (algebraMap Q L)
  have he (μ : T.charpoly.rootSet L) : Module.End.HasEigenvalue U.mulVecLin μ.val := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_mulVecLin]
    change (T.map (algebraMap Q L)).charpoly.IsRoot _
    rw [charpoly_map]
    simpa only [IsRoot, eval_map, aeval_def] using (mem_rootSet.mp μ.property).2
  choose v hv using fun μ => (he μ).exists_hasEigenvector
  have hvi : LinearIndependent L v :=
    Module.End.eigenvectors_linearIndependent' U.mulVecLin _ Subtype.val_injective v hv
  have hc : Fintype.card (T.charpoly.rootSet L) = Module.finrank L (ι → L) := by
    rw [card_rootSet_eq_natDegree hsep hsplit, T.charpoly_natDegree_eq_dim,
      Module.finrank_fintype_fun_eq_card]
  let b := basisOfLinearIndependentOfCardEqFinrank' v hvi hc
  refine ⟨b, fun μ => ?_⟩
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank', U, Matrix.mulVecLin_apply] using (hv μ).apply_eq_smul
end Eigenbasis

section NonzeroCoordinates
variable {Q L ι γ : Type*} [Field Q] [Infinite Q] [Field L] [Algebra Q L]
  [Fintype ι] [DecidableEq ι] [Finite γ]

theorem exists_ground_vector_all_coords_ne_zero (b : Basis γ L (ι → L)) :
    ∃ v : ι → Q, ∀ j, b.repr (algebraMap Q L ∘ v) j ≠ 0 := by
  classical
  let c : (ι → Q) →ₗ[Q] (ι → L) :=
    { toFun := fun v => (algebraMap Q L) ∘ v
      map_add' := by intro x y; ext; simp
      map_smul' := by intro a x; ext; simp [Algebra.smul_def] }
  let p (j : γ) := LinearMap.ker ((b.coord j).restrictScalars Q |>.comp c)
  have hp (j : γ) : p j ≠ ⊤ := by
    intro h
    have hz (i : ι) : b.repr (Pi.single i 1) j = 0 := by
      have he : Pi.single i 1 ∈ p j := h ▸ Submodule.mem_top
      change b.repr (algebraMap Q L ∘ Pi.single i 1) j = 0 at he
      have hc : algebraMap Q L ∘ Pi.single i (1 : Q) = Pi.single i (1 : L) := by
        ext x; simp [Pi.single_apply, apply_ite]
      simpa only [hc] using he
    have hh : b.repr (b j) j = 0 := by
      have hb : b j = ∑ i, (b j i) • Pi.single i (1 : L) := by
        ext i; simp [Pi.single_apply]
      rw [hb, map_sum, Finsupp.finsetSum_apply]
      simp [hz]
    simp at hh
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  exact ⟨v, hv⟩
end NonzeroCoordinates
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section Coordinates
variable {L V γ : Type*} [Field L] [AddCommGroup V] [Module L V]
variable (b : Basis γ L V) (φ : V →ₗ[L] V) (μ : γ → L)
variable (hφ : ∀ i, φ (b i) = μ i • b i)

include hφ in
theorem eigenbasis_coord_apply (j : γ) (x : V) :
    b.coord j (φ x) = μ j * b.coord j x := by
  classical
  have he : (b.coord j).comp φ = μ j • b.coord j := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, hφ, map_smul, LinearMap.smul_apply,
      Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with h
    · subst i; rfl
    · simp
  exact congrArg (fun f : V →ₗ[L] L => f x) he

include hφ in
theorem eigenbasis_coord_pow (j : γ) (x : V) (n : ℕ) :
    b.coord j ((φ ^ n) x) = μ j ^ n * b.coord j x := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, eigenbasis_coord_apply b φ μ hφ,
      hn, pow_succ', mul_assoc]

include hφ in
theorem eigenbasis_coord_aeval (j : γ) (x : V) (p : L[X]) :
    b.coord j ((aeval φ p) x) = p.eval (μ j) * b.coord j x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq, add_mul]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, eigenbasis_coord_pow b φ μ hφ, eval_monomial, smul_eq_mul,
      mul_assoc]
end Coordinates
section Extension
variable {Q L ι : Type*} [Field Q] [Field L] [Algebra Q L]
  [Fintype ι] [DecidableEq ι]

theorem matrix_aeval_mulVec (T : Matrix ι ι Q) (p : Q[X]) (v : ι → Q) :
    (aeval T.mulVecLin p) v = (aeval T p) *ᵥ v := by
  have h := Polynomial.aeval_algHom_apply
    (Matrix.toLinAlgEquiv' (R := Q) (n := ι)) T p
  exact congrArg (fun f : (ι → Q) →ₗ[Q] (ι → Q) => f v) h

theorem matrix_aeval_map_mulVec (T : Matrix ι ι Q) (p : Q[X]) (v : ι → Q) :
    algebraMap Q L ∘ ((aeval T.mulVecLin p) v) =
      (aeval (T.map (algebraMap Q L)).mulVecLin (p.map (algebraMap Q L)))
        (algebraMap Q L ∘ v) := by
  rw [matrix_aeval_mulVec, matrix_aeval_mulVec]
  have hm : (aeval T p).map (algebraMap Q L) =
      aeval (T.map (algebraMap Q L)) (p.map (algebraMap Q L)) := by
    apply Polynomial.map_aeval_eq_aeval_map (R := Q) (S := Matrix ι ι Q)
      (T := L) (U := Matrix ι ι L) (φ := algebraMap Q L)
      (ψ := (algebraMap Q L).mapMatrix)
    ext c i j
    simp only [RingHom.comp_apply, Matrix.algebraMap_matrix_apply,
      Algebra.algebraMap_self, Matrix.map_apply, RingHom.mapMatrix_apply]
    split_ifs <;> simp_all
  rw [← hm]
  funext i
  exact (algebraMap Q L).map_mulVec (aeval T p) v i
end Extension
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section
variable {Q ι : Type*} [Field Q] [Fintype ι] [DecidableEq ι]

theorem cyclicMap_root_mul (T : Matrix ι ι Q) (v : ι → Q)
    (x : AdjoinRoot T.charpoly) :
    cyclicMap T v (AdjoinRoot.root T.charpoly * x) = T *ᵥ cyclicMap T v x := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  change cyclicMap T v (AdjoinRoot.mk T.charpoly X * AdjoinRoot.mk T.charpoly p) = _
  rw [← map_mul, cyclicMap_mk, map_mul, aeval_X, Module.End.mul_apply, cyclicMap_mk]
  rfl
end
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section
variable {Q ι : Type*} [Field Q] [Infinite Q] [Fintype ι] [DecidableEq ι]

theorem exists_cyclicMap_bijective (T : Matrix ι ι Q)
    (hsep : T.charpoly.Separable) :
    ∃ v : ι → Q, Function.Bijective (cyclicMap T v) := by
  let L := T.charpoly.SplittingField
  obtain ⟨b, hb⟩ := exists_splitting_eigenbasis (L := L) T hsep
    (SplittingField.splits T.charpoly)
  obtain ⟨v, hv⟩ := exists_ground_vector_all_coords_ne_zero (Q := Q) b
  have hi : Function.Injective (cyclicMap T v) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    apply rootEvaluation_injective T.charpoly_monic hsep (SplittingField.splits T.charpoly)
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [cyclicMap_mk] at hz
    funext μ
    rw [rootEvaluation_mk, map_zero, Pi.zero_apply]
    have hve : (aeval (T.map (algebraMap Q L)).mulVecLin (p.map (algebraMap Q L)))
        (algebraMap Q L ∘ v) = 0 := by
      rw [← matrix_aeval_map_mulVec, hz]
      ext i; simp
    have he := eigenbasis_coord_aeval b (T.map (algebraMap Q L)).mulVecLin
      (fun μ => μ.val) (fun μ => by simpa using hb μ) μ
      (algebraMap Q L ∘ v) (p.map (algebraMap Q L))
    rw [hve, map_zero] at he
    have hp : aeval μ.val p * (b.repr (algebraMap Q L ∘ v)) μ = 0 := by
      simpa only [eval_map, aeval_def, Basis.coord_apply] using he.symm
    exact (mul_eq_zero.mp hp).resolve_right (hv μ)
  let : Module.Finite Q (AdjoinRoot T.charpoly) := T.charpoly_monic.finite_adjoinRoot
  have hd : Module.finrank Q (AdjoinRoot T.charpoly) = Module.finrank Q (ι → Q) := by
    rw [show Module.finrank Q (AdjoinRoot T.charpoly) = T.charpoly.natDegree from
      finrank_quotient_span_eq_natDegree, T.charpoly_natDegree_eq_dim,
      Module.finrank_fintype_fun_eq_card]
  exact ⟨v, hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

theorem exists_generic_matrix_equiv (T : Matrix ι ι Q)
    (hsep : T.charpoly.Separable) :
    ∃ e : (ι → Q) ≃ₗ[Q] AdjoinRoot T.charpoly,
      ∀ x, e (T *ᵥ x) = AdjoinRoot.root T.charpoly * e x := by
  obtain ⟨v, hv⟩ := exists_cyclicMap_bijective T hsep
  let e := LinearEquiv.ofBijective (cyclicMap T v) hv
  refine ⟨e.symm, fun x => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply]
  change T *ᵥ x = cyclicMap T v (AdjoinRoot.root T.charpoly * e.symm x)
  rw [cyclicMap_root_mul]
  exact congrArg T.mulVec (e.apply_symm_apply x).symm
end
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
-- module Solutions.OAIQW_PermanentBorder.ConductorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Conductor
section Coordinate
variable {O L ι : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  [Field L] [Algebra O L] [IsFractionRing O L] [Finite ι]

theorem principal_coordinate (w : ι → L) (hw : ∃ i, w i ≠ 0) :
    ∃ g : L, g ≠ 0 ∧ ∃ c : ι → O,
      (∀ i, w i = algebraMap O L (c i) * g) ∧ Ideal.span (Set.range c) = ⊤ := by
  classical
  let M := Submodule.span O (Set.range w)
  have hfg : M.FG := Submodule.fg_span (Set.finite_range w)
  let I : FractionalIdeal (nonZeroDivisors O) L :=
    ⟨M, FractionalIdeal.isFractional_of_fg hfg⟩
  have : M.IsPrincipal := FractionalIdeal.isPrincipal I
  let g := Submodule.IsPrincipal.generator M
  have hg : g ≠ 0 := by
    intro hz
    have hm : M = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero M).mpr hz
    obtain ⟨i, hi⟩ := hw
    apply hi
    have hwi : w i ∈ M := Submodule.subset_span (Set.mem_range_self i)
    simpa [hm] using hwi
  have hc (i : ι) : ∃ c : O, w i = c • g :=
    (Submodule.IsPrincipal.mem_iff_eq_smul_generator M).mp
      (Submodule.subset_span (Set.mem_range_self i))
  choose c hc using hc
  refine ⟨g, hg, c, (fun i => by simpa [Algebra.smul_def] using hc i), ?_⟩
  let J := Ideal.span (Set.range c)
  have hrep (x : L) (hx : x ∈ M) : ∃ a : O, a ∈ J ∧ x = a • g := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨c i, Ideal.subset_span (Set.mem_range_self i), hc i⟩
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, J.add_mem ha hb, (add_smul _ _ _).symm⟩
    | smul a x _ hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨a * b, J.mul_mem_left a hb, (mul_smul _ _ _).symm⟩
  obtain ⟨a, ha, he⟩ := hrep g (Submodule.IsPrincipal.generator_mem M)
  have he' : algebraMap O L a = 1 := by
    apply (mul_right_inj' hg).mp
    simpa [Algebra.smul_def, mul_comm] using he.symm
  have ha1 : a = 1 := (IsFractionRing.injective O L) (by simpa using he')
  exact Ideal.eq_top_of_isUnit_mem J (ha1 ▸ ha) isUnit_one
end Coordinate

open scoped BigOperators
section GenericCombination
variable {K O ι γ : Type*} [Field K] [Infinite K] [CommRing O] [Algebra K O]
  [Fintype ι] [Finite γ] [Finite (MaximalSpectrum O)]

theorem simultaneous_unit_combination (v : γ → ι → O)
    (hv : ∀ j, Ideal.span (Set.range (v j)) = ⊤) :
    ∃ a : ι → K, ∀ j, IsUnit (∑ i, algebraMap K O (a i) * v j i) := by
  classical
  let ℓ (j : γ) : (ι → K) →ₗ[K] O :=
    { toFun := fun a => ∑ i, a i • v j i
      map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [smul_smul, Finset.smul_sum] }
  let p (j : γ × MaximalSpectrum O) : Submodule K (ι → K) :=
    (j.2.asIdeal.restrictScalars K).comap (ℓ j.1)
  have hp (j : γ × MaximalSpectrum O) : p j ≠ ⊤ := by
    intro h
    have hm : Ideal.span (Set.range (v j.1)) ≤ j.2.asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have ht : Pi.single i (1 : K) ∈ p j := by rw [h]; trivial
      change (∑ t, (Pi.single i (1 : K) : ι → K) t • v j.1 t) ∈ j.2.asIdeal at ht
      simpa using ht
    rw [hv] at hm
    exact j.2.isMaximal.ne_top (top_le_iff.mp hm)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨a, fun j => ?_⟩
  by_contra hu
  obtain ⟨M, hM, hvM⟩ := exists_max_ideal_of_mem_nonunits hu
  exact ha (j, ⟨M, hM⟩) (by simpa only [p, Submodule.mem_comap,
    Submodule.restrictScalars_mem, LinearMap.coe_mk, AddHom.coe_mk, ℓ,
    Algebra.smul_def] using hvM)
end GenericCombination

section Ratios
variable {K O L ι γ : Type*} [Field K] [Infinite K]
  [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra K O]
  [Field L] [Algebra O L] [IsFractionRing O L] [Algebra K L] [IsScalarTower K O L]
  [Fintype ι] [Finite γ] [Finite (MaximalSpectrum O)]

theorem simultaneous_coordinate_generator (w : ι → γ → L)
    (hw : ∀ j, ∃ i, w i j ≠ 0) :
    ∃ a : ι → K,
      (∀ j, (∑ i, algebraMap K L (a i) * w i j) ≠ 0) ∧
      ∀ i j, ∃ c : O, w i j = algebraMap O L c *
        (∑ t, algebraMap K L (a t) * w t j) := by
  classical
  choose g hg c hc hspan using fun j => principal_coordinate (O := O) (fun i => w i j) (hw j)
  obtain ⟨a, ha⟩ := simultaneous_unit_combination (K := K) c hspan
  let u (j : γ) : Oˣ := (ha j).unit
  have hu (j : γ) : (u j : O) = ∑ i, algebraMap K O (a i) * c j i := (ha j).unit_spec
  have hh (j : γ) : (∑ i, algebraMap K L (a i) * w i j) =
      algebraMap O L (u j) * g j := by
    rw [hu, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, ← IsScalarTower.algebraMap_apply K O L, hc]
    ring
  refine ⟨a, fun j => ?_, fun i j => ?_⟩
  · rw [hh]
    exact mul_ne_zero ((u j).isUnit.map (algebraMap O L)).ne_zero (hg j)
  · refine ⟨c j i * ↑(u j)⁻¹, ?_⟩
    rw [hh, hc, map_mul]
    have hi : algebraMap O L (↑(u j)⁻¹ : O) * algebraMap O L (u j) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc
      algebraMap O L (c j i) * g j =
          algebraMap O L (c j i) * (1 * g j) := by rw [one_mul]
      _ = _ := by rw [← hi]; ring
end Ratios
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
section Coordinates
variable {S A L γ : Type*} [CommRing S] [CommRing A] [Field L]
  [Algebra S A] [Algebra S L] [Finite γ]
  [Module.Finite S (integralClosure S L)]

theorem isIntegral_of_coordinates (f : A →ₐ[S] (γ → L))
    (hf : Function.Injective f) {x : A} (hx : ∀ j, IsIntegral S (f x j)) :
    IsIntegral S x := by
  let z : γ → integralClosure S L := fun j => ⟨f x j, hx j⟩
  let ρ : (γ → integralClosure S L) →ₐ[S] (γ → L) :=
    AlgHom.pi fun j => (integralClosure S L).val.comp
      (Pi.evalAlgHom S (fun _ : γ => integralClosure S L) j)
  have hz : IsIntegral S z := Algebra.IsIntegral.isIntegral z
  have hr : ρ z = f x := rfl
  exact (isIntegral_algHom_iff f hf).mp (hr ▸ hz.map ρ)
end Coordinates

section UnitCoordinates
variable {Q A L γ : Type*} [Field Q] [CommRing A] [Field L]
  [Algebra Q A] [Algebra Q L] [Module.Finite Q A]

theorem isUnit_of_coordinates (f : A →ₐ[Q] (γ → L))
    (hf : Function.Injective f) {x : A} (hx : ∀ j, f x j ≠ 0) : IsUnit x := by
  have : IsArtinianRing A := IsArtinianRing.of_finite Q A
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  apply hf
  ext j
  have h := congrFun (congrArg f hz) j
  simpa only [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply,
    mul_eq_zero, hx j, or_false] using h
end UnitCoordinates
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open scoped BigOperators
section NormalizedLattice
variable {K S Q A L ι γ : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S] [Algebra K S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [CommRing A] [Algebra Q A] [Algebra S A] [IsScalarTower S Q A]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [Algebra K L] [IsScalarTower K S L]
  [Module.Finite Q A] [FiniteDimensional Q L] [Algebra.IsSeparable Q L]
  [Fintype ι] [Finite γ]

include K in

theorem exists_normalizing_lattice_element (f : A →ₐ[Q] (γ → L))
    (hf : Function.Injective f) (l : ι → A)
    (hl : ∀ j, ∃ i, f (l i) j ≠ 0) :
    ∃ u : Aˣ, (u : A) ∈ Submodule.span S (Set.range l) ∧
      ∀ x ∈ Submodule.span S (Set.range l), IsIntegral S ((↑u⁻¹ : A) * x) := by
  classical
  let O := integralClosure S L
  have : Module.Finite S O := IsIntegralClosure.finite S Q L O
  have : IsPrincipalIdealRing O := integralClosure_isPrincipalIdealRing (Q := Q)
  have : Finite (MaximalSpectrum O) := finite_maximalSpectrum_of_finite_local (S := S)
  have : IsFractionRing O L := IsIntegralClosure.isFractionRing_of_finite_extension S Q L O
  let : Algebra K O := ((integralClosure S L).restrictScalars K).algebra
  have : IsScalarTower K O L := IsScalarTower.of_algebraMap_eq fun x => rfl
  obtain ⟨a, ha, hrat⟩ := simultaneous_coordinate_generator (K := K) (O := O)
    (fun i j => f (l i) j) hl
  let h : A := ∑ i, algebraMap K S (a i) • l i
  have hh (j : γ) : f h j = ∑ i, algebraMap K L (a i) * f (l i) j := by
    change (f.restrictScalars S) h j = _
    simp [h, Algebra.smul_def, ← IsScalarTower.algebraMap_apply K S L]
  have hu : IsUnit h := isUnit_of_coordinates f hf (fun j => hh j ▸ ha j)
  let u := hu.unit
  have huval : (u : A) = h := hu.unit_spec
  have hmem : h ∈ Submodule.span S (Set.range l) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨u, huval.symm ▸ hmem, ?_⟩
  have hli (i : ι) : IsIntegral S ((↑u⁻¹ : A) * l i) := by
    apply isIntegral_of_coordinates (f.restrictScalars S) hf
    intro j
    obtain ⟨c, hc⟩ := hrat i j
    have he : f ((↑u⁻¹ : A) * l i) j = algebraMap O L c := by
      rw [map_mul, Pi.mul_apply, hc, ← hh j, ← huval]
      have hinv : f (↑u⁻¹ : A) j * f (u : A) j = 1 := by
        have hi := congrFun (congrArg f (Units.inv_mul u)) j
        simpa only [map_mul, map_one, Pi.mul_apply, Pi.one_apply] using hi
      calc
        f (↑u⁻¹ : A) j * (algebraMap O L c * f (u : A) j) =
          algebraMap O L c * (f (↑u⁻¹ : A) j * f (u : A) j) := by ring
        _ = algebraMap O L c := by rw [hinv, mul_one]
    change IsIntegral S (f ((↑u⁻¹ : A) * l i) j)
    rw [he]
    exact c.property
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hli i
  | zero => simpa using (isIntegral_zero : IsIntegral S (0 : A))
  | add x y _ _ hx hy => simpa only [mul_add] using hx.add hy
  | smul s x _ hx =>
    simpa only [mul_smul_comm] using hx.smul s
end NormalizedLattice
end PermanentBorder.Conductor
namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section MatrixGenerators
variable {K S Q ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S] [Algebra K S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Fintype ι] [DecidableEq ι]

include K in

theorem exists_normalizing_matrix_generators (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S Q)).Separable) :
    ∃ (l : ι → AdjoinRoot (T.charpoly.map (algebraMap S Q)))
      (u : (AdjoinRoot (T.charpoly.map (algebraMap S Q)))ˣ),
      (∀ j, genericBaseChange (Q := Q) T.charpoly (AdjoinRoot.root T.charpoly) * l j =
        ∑ i, algebraMap S (AdjoinRoot (T.charpoly.map (algebraMap S Q))) (T i j) * l i) ∧
      (u : AdjoinRoot (T.charpoly.map (algebraMap S Q))) ∈
        Submodule.span S (Set.range l) ∧
      ∀ x ∈ Submodule.span S (Set.range l), IsIntegral S ((↑u⁻¹) * x) := by
  classical
  let : Algebra K Q := ((algebraMap S Q).comp (algebraMap K S)).toAlgebra
  let : IsScalarTower K S Q := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : Infinite Q := Infinite.of_injective (algebraMap K Q) (algebraMap K Q).injective
  let f := T.charpoly.map (algebraMap S Q)
  let A := AdjoinRoot f
  let L := f.SplittingField
  have : IsScalarTower K S L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K Q L, IsScalarTower.algebraMap_apply S Q L,
      IsScalarTower.algebraMap_apply K S Q]
  have : Module.Finite Q A := (T.charpoly_monic.map _).finite_adjoinRoot
  have : Algebra.IsSeparable Q L := Algebra.isSeparable_of_separable_splitting_field Q L hsep
  obtain ⟨e, he⟩ : ∃ e : (ι → Q) ≃ₗ[Q] A,
      ∀ x, e ((T.map (algebraMap S Q)) *ᵥ x) = AdjoinRoot.root f * e x := by
    have hs : (T.map (algebraMap S Q)).charpoly.Separable := by
      simpa only [charpoly_map] using hsep
    obtain ⟨e₀, he₀⟩ := exists_generic_matrix_equiv (T.map (algebraMap S Q)) hs
    let a := AdjoinRoot.algEquivOfEq Q (T.map (algebraMap S Q)).charpoly f
      (charpoly_map T (algebraMap S Q))
    refine ⟨e₀.trans a.toLinearEquiv, fun x => ?_⟩
    change a (e₀ _) = AdjoinRoot.root f * a (e₀ x)
    rw [he₀, map_mul, show a (AdjoinRoot.root (T.map (algebraMap S Q)).charpoly) =
      AdjoinRoot.root f from AdjoinRoot.algEquivOfEq_root (R := Q) _ _ _]
  let l : ι → A := fun i => e (Pi.single i 1)
  have hsum (x : ι → Q) : e x = ∑ i, x i • l i := by
    have hx : x = ∑ i, x i • Pi.single i (1 : Q) := by
      ext j; simp [Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, l]
  have hl (j : f.rootSet L) : ∃ i, rootEvaluation (f := f) (L := L) (l i) j ≠ 0 := by
    by_contra hn
    push Not at hn
    have h := congrFun (congrArg (rootEvaluation (f := f) (L := L)) (hsum (e.symm 1))) j
    rw [e.apply_symm_apply] at h
    simp [hn] at h
  obtain ⟨u, hu, hnorm⟩ := exists_normalizing_lattice_element (K := K) (S := S)
    (rootEvaluation (f := f) (L := L))
    (rootEvaluation_injective (T.charpoly_monic.map _) hsep (SplittingField.splits f)) l hl
  refine ⟨l, u, ?_, hu, hnorm⟩
  intro j
  have hg : genericBaseChange (Q := Q) T.charpoly (AdjoinRoot.root T.charpoly) =
      AdjoinRoot.root f := by
    simpa only [AdjoinRoot.root, Polynomial.map_X] using
      genericBaseChange_mk (Q := Q) T.charpoly X
  rw [hg, ← he, hsum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    Matrix.map_apply, Algebra.smul_def, ← IsScalarTower.algebraMap_apply S Q A]
  rfl
end MatrixGenerators
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Matrix Polynomial

section MatrixFactorization
variable {R ι : Type*} [CommRing R] [IsDomain R]
  [Fintype ι] [DecidableEq ι]

theorem kernel_eq_adjugate_image (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (v : ι → DetQuotient M) :
    (M.map (Ideal.Quotient.mk (Ideal.span {M.det}))) *ᵥ v = 0 ↔
      ∃ w : ι → DetQuotient M,
        (M.adjugate.map (Ideal.Quotient.mk (Ideal.span {M.det}))) *ᵥ w = v := by
  classical
  let π : R →+* DetQuotient M := Ideal.Quotient.mk _
  constructor
  · intro hv
    change (M.map π) *ᵥ v = 0 at hv
    obtain ⟨b, hb⟩ : ∃ b : ι → R, ∀ i, π (b i) = v i := by
      choose b hb using (fun i => Ideal.Quotient.mk_surjective (v i))
      exact ⟨b, hb⟩
    have hdiv (i : ι) : M.det ∣ (M *ᵥ b) i := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hm := π.map_mulVec M b i
      rw [show (π ∘ b) = v by funext j; exact hb j] at hm
      simpa only [hv, Pi.zero_apply, Function.comp_apply] using hm
    choose c hc using hdiv
    have hMc : M *ᵥ b = M.det • c := by funext i; exact hc i
    have hid : M.det • b = M.det • (M.adjugate *ᵥ c) := by
      calc
        M.det • b = M.adjugate *ᵥ (M *ᵥ b) := by
          rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
        _ = M.det • (M.adjugate *ᵥ c) := by rw [hMc, mulVec_smul]
    have hb' : M.adjugate *ᵥ c = b := by
      funext i
      exact (mul_left_cancel₀ hM (congrFun hid i)).symm
    refine ⟨π ∘ c, ?_⟩
    funext i
    change (M.adjugate.map π *ᵥ (π ∘ c)) i = v i
    rw [← π.map_mulVec, hb']
    exact hb i
  · rintro ⟨w, rfl⟩
    change (M.map π) *ᵥ ((M.adjugate.map π) *ᵥ w) = 0
    rw [mulVec_mulVec, ← Matrix.map_mul, mul_adjugate]
    have hd : π M.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton M.det))
    have hz : (M.det • (1 : Matrix ι ι R)).map π = 0 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hd, zero_mul,
        Matrix.zero_apply]
    rw [hz, zero_mulVec]

theorem row_kernel_eq_adjugate_image (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (v : ι → DetQuotient M) :
    v ᵥ* (M.map (Ideal.Quotient.mk (Ideal.span {M.det}))) = 0 ↔
      ∃ w : ι → DetQuotient M,
        w ᵥ* (M.adjugate.map (Ideal.Quotient.mk (Ideal.span {M.det}))) = v := by
  have ht := kernel_eq_adjugate_image Mᵀ (by simpa using hM)
  dsimp only [DetQuotient] at ht
  rw [det_transpose] at ht
  simp only [← adjugate_transpose, Matrix.transpose_map, mulVec_transpose] at ht
  exact ht v

end MatrixFactorization

end PermanentBorder.Conductor
namespace PermanentBorder.Conductor
open Matrix Polynomial
section
variable {S ι A : Type*} [CommRing S] [IsDomain S]
  [Fintype ι] [DecidableEq ι] [CommRing A] [Algebra S A]

omit [IsDomain S] in
theorem mapped_charmatrix (T : Matrix ι ι S) :
    T.charmatrix.map (AdjoinRoot.mk T.charpoly) =
      Matrix.scalar ι (AdjoinRoot.root T.charpoly) -
        T.map (algebraMap S (AdjoinRoot T.charpoly)) := by
  ext i j
  simp only [charmatrix, Matrix.map_apply, Matrix.sub_apply, map_sub,
    Matrix.scalar_apply, Matrix.diagonal_apply, AdjoinRoot.root]
  split_ifs <;> rfl

theorem conductor_mem_adjugate_of_lattice (T : Matrix ι ι S)
    (g : AdjoinRoot T.charpoly →ₐ[S] A) (hg : Function.Injective g)
    (l : ι → A)
    (hl : ∀ j, g (AdjoinRoot.root T.charpoly) * l j =
      ∑ i, algebraMap S A (T i j) * l i)
    (u : Aˣ) (hu : (u : A) ∈ Submodule.span S (Set.range l))
    (hnorm : ∀ x ∈ Submodule.span S (Set.range l), IsIntegral S ((↑u⁻¹ : A) * x))
    (a : AdjoinRoot T.charpoly)
    (ha : ∀ x : A, IsIntegral S x → ∃ b : AdjoinRoot T.charpoly,
      g b = g a * x) :
    a ∈ matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
  classical
  have hex (i : ι) : ∃ r : AdjoinRoot T.charpoly,
      g r = g a * ((↑u⁻¹ : A) * l i) :=
    ha _ (hnorm _ (Submodule.subset_span ⟨i, rfl⟩))
  choose r hr using hex
  have hrow : r ᵥ* T.charmatrix.map (AdjoinRoot.mk T.charpoly) = 0 := by
    rw [mapped_charmatrix, vecMul_sub]
    apply sub_eq_zero.mpr
    ext j
    simp only [scalar_apply]
    rw [vecMul_diagonal]
    simp only [vecMul, dotProduct]
    apply hg
    simp only [map_mul, map_sum, hr, AlgHom.commutes, Matrix.map_apply]
    calc
      (g a * ((↑u⁻¹ : A) * l j)) * g (AdjoinRoot.root T.charpoly) =
          (g a * (↑u⁻¹ : A)) * (g (AdjoinRoot.root T.charpoly) * l j) := by ring
      _ = (g a * (↑u⁻¹ : A)) * ∑ i, algebraMap S A (T i j) * l i := by rw [hl]
      _ = ∑ i, (g a * ((↑u⁻¹ : A) * l i)) * algebraMap S A (T i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  obtain ⟨w, hw⟩ := (row_kernel_eq_adjugate_image T.charmatrix T.charpoly_monic.ne_zero r).mp hrow
  have hrmem (j : ι) : r j ∈
      matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
    rw [← hw]
    exact Ideal.sum_mem _ (fun i _ =>
      Ideal.mul_mem_left _ (w i) (entry_mem_matrixEntryIdeal _ i j))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hu
  have hae : a = ∑ i, algebraMap S (AdjoinRoot T.charpoly) (c i) * r i := by
    apply hg
    simp only [map_sum, map_mul, AlgHom.commutes, hr]
    have hc' : ∑ i, algebraMap S A (c i) * l i = (u : A) := by
      simpa only [Algebra.smul_def] using hc
    calc
      g a = (g a * (↑u⁻¹ : A)) * (u : A) := by simp [mul_assoc]
      _ = (g a * (↑u⁻¹ : A)) * ∑ i, algebraMap S A (c i) * l i := by rw [hc']
      _ = ∑ i, algebraMap S A (c i) * (g a * ((↑u⁻¹ : A) * l i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hae]
  exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (hrmem i))
end
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
open Polynomial Matrix Module
section LocalComparison
variable {K S Q ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S] [Algebra K S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Fintype ι] [DecidableEq ι]

include K in

theorem normalization_conductor_le_adjugate (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S Q)).Separable) :
    letI := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
    algebraConductor (AdjoinRoot T.charpoly)
      (integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S Q)))) ≤
      matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  obtain ⟨l, u, hl, hu, hnorm⟩ := exists_normalizing_matrix_generators (K := K) T hsep
  intro a ha
  apply conductor_mem_adjugate_of_lattice T (genericBaseChange (Q := Q) T.charpoly)
    (genericBaseChange_injective (Q := Q) T.charpoly T.charpoly_monic) l hl u hu hnorm a
  intro x hx
  obtain ⟨b, hb⟩ := ha (⟨x, hx⟩ : integralClosure S
    (AdjoinRoot (T.charpoly.map (algebraMap S Q))))
  exact ⟨b, congrArg Subtype.val hb⟩

end LocalComparison
end PermanentBorder.Conductor

namespace PermanentBorder.RootLocalization
open Polynomial

section BaseChange
variable {S U : Type*} [CommRing S] [CommRing U] [Algebra S U]
variable (f : S[X]) (g : U[X]) (hfg : f.map (algebraMap S U) = g)

theorem changeRoot_injective (hf : f.Monic)
    (hSU : Function.Injective (algebraMap S U)) :
    Function.Injective (changeRoot f g hfg) := by
  subst g
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [changeRoot_mk, AdjoinRoot.mk_eq_zero] at hz
  rw [AdjoinRoot.mk_eq_zero, ← modByMonic_eq_zero_iff_dvd hf]
  apply Polynomial.map_injective (algebraMap S U) hSU
  rw [Polynomial.map_zero, map_modByMonic _ hf,
    (modByMonic_eq_zero_iff_dvd (hf.map _)).mpr hz]

variable (M : Submonoid S) [IsLocalization M U]

theorem changeRoot_denominators (x : AdjoinRoot g) :
    ∃ s : M, ∃ b : AdjoinRoot f, s • x = changeRoot f g hfg b := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨s, hs, hp⟩ := IsLocalization.integerNormalization_spec M p
  refine ⟨⟨s, hs⟩, AdjoinRoot.mk f (IsLocalization.integerNormalization M p), ?_⟩
  rw [changeRoot_mk, hp]
  exact (map_smul (((AdjoinRoot.mkₐ g).restrictScalars S).toLinearMap) s p).symm

theorem changeRoot_isLocalizedModule (hf : f.Monic) (hM : M ≤ nonZeroDivisors S) :
    IsLocalizedModule M (changeRoot f g hfg).toLinearMap where
  map_units s := by
    have h := (IsLocalization.map_units U s).map (Algebra.lsmul S S (AdjoinRoot g)).toRingHom
    convert h using 1
    ext z
    change (s : S) • z = (algebraMap S U (s : S)) • z
    exact (algebraMap_smul U (s : S) z).symm
  surj x := by
    obtain ⟨s, b, hb⟩ := changeRoot_denominators f g hfg M x
    exact ⟨⟨b,s⟩, hb⟩
  exists_of_eq h := by
    refine ⟨1, ?_⟩
    simpa only [one_smul] using
      changeRoot_injective f g hfg hf (IsLocalization.injective U hM) h

end BaseChange
end PermanentBorder.RootLocalization

namespace PermanentBorder.ConductorLocalization
section
variable {S U B C E : Type*} [CommRing S] [CommRing U] [CommRing B]
  [CommRing C] [CommRing E] [Algebra S U] [Algebra S B] [Algebra S C]
  [Algebra U C] [IsScalarTower S U C] [Algebra S E] [Algebra U E]
  [IsScalarTower S U E]
variable (M : Submonoid S) [IsLocalization M U]

include M in

theorem integral_conductor_localizes (j : B →ₐ[S] C) (g : B →ₐ[S] E)
    (q : C →ₐ[U] E) (hcomp : (q.restrictScalars S).comp j = g)
    (b : B) (hb : ∀ x : E, IsIntegral S x → ∃ a : B, g a = g b * x) :
    ∀ x : E, IsIntegral U x → ∃ a : C, q a = q (j b) * x := by
  intro x hx
  obtain ⟨s, hs⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (M := M) x hx
  obtain ⟨a, ha⟩ := hb ((s : S) • x) hs
  obtain ⟨u, hu⟩ := IsLocalization.map_units U s
  have hu' : (u : U) = algebraMap S U (s : S) := hu
  refine ⟨(↑u⁻¹ : U) • j a, ?_⟩
  have hj (a : B) : q (j a) = g a := AlgHom.congr_fun hcomp a
  rw [map_smul, hj, ha, mul_smul_comm, ← hj b]
  rw [← algebraMap_smul U (s : S), ← hu', smul_smul]
  simp
end
end PermanentBorder.ConductorLocalization

namespace PermanentBorder.IdealLocalization
section
variable {S B C : Type*} [CommRing S] [CommRing B] [CommRing C]
  [Algebra S B] [Algebra S C]
variable (M : Submonoid S) (j : B →ₐ[S] C) [IsLocalizedModule M j.toLinearMap]

theorem map_le_localizedIdeal (I : Ideal B) :
    I.map j.toRingHom ≤ localizedIdeal M j I := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact ⟨x,hx,1, by simp⟩

theorem map_mem_localized (I : Ideal B) (x : C)
    (hx : x ∈ I.map j.toRingHom) :
    x ∈ (I.restrictScalars S).localized₀ M j.toLinearMap :=
  map_le_localizedIdeal M j I hx
end
end PermanentBorder.IdealLocalization

namespace PermanentBorder.Conductor
open Polynomial Matrix RootLocalization
section
variable {S U ι : Type*} [CommRing S] [CommRing U] [Algebra S U]
  [Fintype ι] [DecidableEq ι]

theorem matrixRootChange_adjugate (T : Matrix ι ι S) :
    (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)).map
      (matrixRootChange (U := U) T) =
    (T.map (algebraMap S U)).charmatrix.adjugate.map
      (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly) := by
  have h1 : T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly) =
      (T.charmatrix.map (AdjoinRoot.mk T.charpoly)).adjugate :=
    (AdjoinRoot.mk T.charpoly).map_adjugate T.charmatrix
  have h2 : (T.charmatrix.map (AdjoinRoot.mk T.charpoly)).adjugate.map
      (matrixRootChange (U := U) T) =
      ((T.charmatrix.map (AdjoinRoot.mk T.charpoly)).map
        (matrixRootChange (U := U) T)).adjugate :=
    (matrixRootChange (U := U) T).map_adjugate _
  have h3 : (T.map (algebraMap S U)).charmatrix.adjugate.map
      (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly) =
      ((T.map (algebraMap S U)).charmatrix.map
        (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly)).adjugate :=
    (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly).map_adjugate _
  rw [h1,h2,h3]
  congr 1
  have hc (x : S) : matrixRootChange (U := U) T (AdjoinRoot.of T.charpoly x) =
      AdjoinRoot.of (T.map (algebraMap S U)).charpoly (algebraMap S U x) :=
    (matrixRootChange (U := U) T).commutes x
  ext i j
  simp only [Matrix.map_apply,charmatrix,Matrix.sub_apply,map_sub,
    Matrix.scalar_apply,Matrix.diagonal_apply]
  split_ifs <;> simp only [RingHom.mapMatrix_apply, Matrix.map_apply, map_zero, AdjoinRoot.mk_X, matrixRootChange_root,
    AdjoinRoot.mk_C, hc]

theorem adjugateIdeal_baseChange (T : Matrix ι ι S) :
    (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).map
      (matrixRootChange (U := U) T).toRingHom =
    matrixEntryIdeal ((T.map (algebraMap S U)).charmatrix.adjugate.map
      (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly)) := by
  rw [matrixEntryIdeal_map]
  congr 1
  exact matrixRootChange_adjugate T
end
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module RootLocalization

section GenericTransport
variable {S U Q ι : Type*} [CommRing S] [CommRing U] [Field Q]
  [Algebra S U] [Algebra S Q] [Algebra U Q] [IsScalarTower S U Q]
  [Fintype ι] [DecidableEq ι]

theorem genericMatrixChange_comp (T : Matrix ι ι S) :
    ((genericBaseChange (Q := Q) (T.map (algebraMap S U)).charpoly).restrictScalars S).comp
      (matrixRootChange (U := U) T) =
    ((genericMatrixChange (U := U) (Q := Q) T).restrictScalars S).toAlgHom.comp
      (genericBaseChange (Q := Q) T.charpoly) := by
  apply AdjoinRoot.algHom_ext
  change genericBaseChange (Q := Q) (T.map (algebraMap S U)).charpoly
      (matrixRootChange (U := U) T (AdjoinRoot.root T.charpoly)) =
    genericMatrixChange (U := U) (Q := Q) T
      (genericBaseChange (Q := Q) T.charpoly (AdjoinRoot.root T.charpoly))
  rw [matrixRootChange_root,genericBaseChange_root,genericBaseChange_root]
  exact (AdjoinRoot.algEquivOfEq_root _ _ _).symm
end GenericTransport

section LocalCondition
variable {K S Q ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S] [Algebra K S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q] [Fintype ι] [DecidableEq ι]

include K in
theorem integral_conductor_le_adjugate_local (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S Q)).Separable)
    (b : AdjoinRoot T.charpoly)
    (hb : ∀ x : AdjoinRoot (T.charpoly.map (algebraMap S Q)), IsIntegral S x →
      ∃ a : AdjoinRoot T.charpoly,
        genericBaseChange (Q := Q) T.charpoly a =
          genericBaseChange (Q := Q) T.charpoly b * x) :
    b ∈ matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  apply normalization_conductor_le_adjugate (K := K) T hsep
  intro x
  obtain ⟨a,ha⟩ := hb x.val x.property
  exact ⟨a,Subtype.ext ha⟩
end LocalCondition

section GlobalComparison
variable {K S ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
  [Fintype ι] [DecidableEq ι]

include K in

theorem normalization_conductor_le_adjugate_global (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S (FractionRing S))).Separable) :
    letI := (normalizationInclusion (Q := FractionRing S) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
    algebraConductor (AdjoinRoot T.charpoly)
      (integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S (FractionRing S))))) ≤
      matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
  let Q := FractionRing S
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  let J := matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))
  intro b hb
  let U (P : Ideal S) [P.IsMaximal] := Localization.AtPrime P
  let C (P : Ideal S) [P.IsMaximal] := AdjoinRoot (T.map (algebraMap S (U P))).charpoly
  let j (P : Ideal S) [P.IsMaximal] : AdjoinRoot T.charpoly →ₐ[S] C P :=
    matrixRootChange (U := U P) T
  have hj (P : Ideal S) [P.IsMaximal] : IsLocalizedModule P.primeCompl (j P).toLinearMap :=
    changeRoot_isLocalizedModule _ _ _ _ T.charpoly_monic P.primeCompl_le_nonZeroDivisors
  apply @Submodule.mem_of_localization_maximal S (AdjoinRoot T.charpoly) _ _ _
    C _ _ (fun P _ => (j P).toLinearMap) hj b (J.restrictScalars S)
  intro P hP
  let := hj P
  let T' := T.map (algebraMap S (U P))
  let e := (genericMatrixChange (U := U P) (Q := Q) T).restrictScalars S
  let g := e.toAlgHom.comp (genericBaseChange (Q := Q) T.charpoly)
  have hbg : ∀ x : AdjoinRoot (T'.charpoly.map (algebraMap (U P) Q)),
      IsIntegral S x → ∃ a : AdjoinRoot T.charpoly, g a = g b * x := by
    intro x hx
    obtain ⟨a,ha⟩ := hb (⟨e.symm x, IsIntegral.map e.symm.toAlgHom hx⟩ :
      integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S Q))))
    have ha0 : genericBaseChange (Q := Q) T.charpoly a =
        genericBaseChange (Q := Q) T.charpoly b * e.symm x := congrArg Subtype.val ha
    have ha' := congrArg e ha0
    refine ⟨a, ?_⟩
    simpa only [g,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,map_mul,AlgEquiv.apply_symm_apply] using ha'
  have hbP := ConductorLocalization.integral_conductor_localizes P.primeCompl (j P) g
    (genericBaseChange (Q := Q) T'.charpoly) (genericMatrixChange_comp T) b hbg
  have hsep' : (T'.charpoly.map (algebraMap (U P) Q)).Separable := by
    rw [← charpoly_map_tower T]
    exact hsep
  have hbJ := integral_conductor_le_adjugate_local (K := K) T' hsep' (j P b) hbP
  apply IdealLocalization.map_mem_localized P.primeCompl (j P) J
  rw [show j P = matrixRootChange (U := U P) T from rfl,adjugateIdeal_baseChange]
  exact hbJ
end GlobalComparison
end PermanentBorder.Conductor

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

namespace PermanentBorder.Conductor
open Polynomial Module Matrix
section ScalarLength
variable {K S ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
  [Fintype ι] [DecidableEq ι]

theorem normalization_adjugate_length_global (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S (FractionRing S))).Separable) :
    let R := integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S (FractionRing S))))
    Module.length K (AdjoinRoot T.charpoly ⧸
      (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).restrictScalars S) ≤
    Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := FractionRing S) T.charpoly T.charpoly_monic).toLinearMap) := by
  let Q := FractionRing S
  let R := integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S Q)))
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  let c := (algebraConductor (AdjoinRoot T.charpoly) R).restrictScalars S
  let J := (matrixEntryIdeal
    (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).restrictScalars S
  have h : c ≤ J := normalization_conductor_le_adjugate_global (K := K) T hsep
  obtain ⟨e⟩ := exists_normalization_conductor_cokernel_equiv T.charpoly_monic hsep
  calc
    _ ≤ Module.length K (AdjoinRoot T.charpoly ⧸ c) :=
      Module.length_le_of_surjective ((Submodule.factor h).restrictScalars K)
        (Submodule.factor_surjective h)
    _ = _ := (e.restrictScalars K).length_eq
end ScalarLength
end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.AdjugateNormalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial

section DiagonalCommutator
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem exists_diagonal_commutator (θ : ι → K) (hθ : Function.Injective θ)
    (Y : Matrix ι ι K) (hY : ∀ i, Y i i = 0) :
    ∃ Z : Matrix ι ι K, Matrix.diagonal θ * Z - Z * Matrix.diagonal θ = Y := by
  let Z : Matrix ι ι K := fun i j => Y i j / (θ i - θ j)
  refine ⟨Z, ?_⟩
  ext i j
  simp only [Matrix.sub_apply]
  rw [Matrix.diagonal_mul θ Z i j, Matrix.mul_diagonal θ Z i j]
  dsimp only [Z]
  by_cases hij : i = j
  · subst j
    simp [hY]
  · have hne : θ i - θ j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hθ h))
    field_simp
end DiagonalCommutator

section Scaling
variable {K : Type*} [Field K] {k : ℕ}

theorem scaledTrace_commutator (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Z : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) :
    scaledTrace θ A (pencilBase θ A * Z - Z * pencilBase θ A) = 0 := by
  unfold scaledTrace
  rw [scaledPencil_eq]
  have hm : (pencilBase θ A * Z - Z * pencilBase θ A).map liftCoefficients =
      (pencilBase θ A).map liftCoefficients * Z.map liftCoefficients -
        Z.map liftCoefficients * (pencilBase θ A).map liftCoefficients := by
    change (liftCoefficients (K := K)).mapMatrix _ = _
    rw [map_sub, map_mul, map_mul]
    rfl
  rw [hm]
  exact trace_commutator_adjugate_scalar _ _ _

theorem scaledTrace_sub (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y Z : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) :
    scaledTrace θ A (Y-Z) = scaledTrace θ A Y - scaledTrace θ A Z := by
  unfold scaledTrace
  have hm : (Y-Z).map liftCoefficients = Y.map liftCoefficients - Z.map liftCoefficients :=
    (liftCoefficients (K := K)).mapMatrix.map_sub Y Z
  rw [hm, sub_mul, Matrix.trace_sub]

theorem pencil_commutator_expand (θ : Fin (k+1) → K)
    (A Z : Matrix (Fin (k+1)) (Fin (k+1)) K) (d : ℕ) :
    pencilBase θ A * ((X : K[X])^d • Z.map C) -
      ((X : K[X])^d • Z.map C) * pencilBase θ A =
      (X : K[X])^(d+1) • (Matrix.diagonal θ * Z - Z * Matrix.diagonal θ).map C +
        (X : K[X])^d • (A * Z - Z * A).map C := by
  simp only [pencilBase, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.map_sub C (map_sub C), Matrix.map_mul, smul_sub, pow_succ]
  rw [mul_comm X (X^d)]
  module

theorem exists_lower_multiplier (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) (d : ℕ)
    (hY : ∀ i j, (Y i j).natDegree ≤ d+1)
    (hT : (scaledTrace θ A Y).natDegree ≤ k) :
    ∃ Y' : Matrix (Fin (k+1)) (Fin (k+1)) K[X],
      (∀ i j, (Y' i j).natDegree ≤ d) ∧ scaledTrace θ A Y' = scaledTrace θ A Y := by
  let Ytop : Matrix (Fin (k+1)) (Fin (k+1)) K := Y.map (fun p => p.coeff (d+1))
  have hz : ∀ i, Ytop i i = 0 := diagonal_top_zero θ hθ A Y (d+1) (by omega) hY hT
  obtain ⟨Z, hZ⟩ := exists_diagonal_commutator θ hθ Ytop hz
  let W := pencilBase θ A * ((X : K[X])^d • Z.map C) -
    ((X : K[X])^d • Z.map C) * pencilBase θ A
  refine ⟨Y-W, ?_, ?_⟩
  · intro i j
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have hW : W = (X : K[X])^(d+1) • Ytop.map C +
        (X : K[X])^d • (A * Z - Z * A).map C := by
      dsimp [W]
      rw [pencil_commutator_expand, hZ]
    rw [Matrix.sub_apply, coeff_sub, hW]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      coeff_add, mul_comm (_^_) (C _), coeff_C_mul, coeff_X_pow]
    by_cases hnd : n = d+1
    · subst n
      simp [Ytop]
    · have hlt : d+1 < n := by omega
      rw [coeff_eq_zero_of_natDegree_lt ((hY i j).trans_lt hlt)]
      simp [hnd, show n≠d by omega]
  · rw [scaledTrace_sub]
    have hzero : scaledTrace θ A W = 0 := scaledTrace_commutator θ A _
    rw [hzero, sub_zero]

theorem exists_constant_multiplier_of_bounded_scaledTrace
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) (d : ℕ)
    (hY : ∀ i j, (Y i j).natDegree ≤ d)
    (hT : (scaledTrace θ A Y).natDegree ≤ k) :
    ∃ Y₀ : Matrix (Fin (k+1)) (Fin (k+1)) K,
      scaledTrace θ A (Y₀.map C) = scaledTrace θ A Y := by
  induction d generalizing Y with
  | zero =>
      refine ⟨Y.map (fun p => p.coeff 0), ?_⟩
      have he : (Y.map (fun p => p.coeff 0)).map C = Y := by
        apply Matrix.ext
        intro i j
        exact (eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (hY i j))).symm
      rw [he]
  | succ d ih =>
      obtain ⟨Y', hY', he⟩ := exists_lower_multiplier θ hθ A Y d hY hT
      have hT' : (scaledTrace θ A Y').natDegree ≤ k := by rw [he]; exact hT
      obtain ⟨Y₀, hY₀⟩ := ih Y' hY' hT'
      exact ⟨Y₀, hY₀.trans he⟩

end Scaling

section OuterVariableReduction
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

namespace HasAdjugateNormalForm
variable {A : Matrix ι ι R} {P Q : R[X]}

theorem zero : HasAdjugateNormalForm A 0 := by
  exact ⟨0, 0, by simp⟩

theorem add (hP : HasAdjugateNormalForm A P) (hQ : HasAdjugateNormalForm A Q) :
    HasAdjugateNormalForm A (P+Q) := by
  obtain ⟨Y,H,rfl⟩ := hP
  obtain ⟨Z,J,rfl⟩ := hQ
  refine ⟨Y+Z,H+J,?_⟩
  rw [adjTrace_add]
  ring

theorem C_mul (hP : HasAdjugateNormalForm A P) (a : R) :
    HasAdjugateNormalForm A (C a * P) := by
  obtain ⟨Y,H,rfl⟩ := hP
  refine ⟨a • Y, C a * H, ?_⟩
  rw [adjTrace_smul]
  ring

theorem X_mul (hP : HasAdjugateNormalForm A P) :
    HasAdjugateNormalForm A (X*P) := by
  obtain ⟨Y,H,rfl⟩ := hP
  refine ⟨-(Y*A), C Y.trace + X*H, ?_⟩
  rw [mul_add, X_mul_adjTrace]
  ring

theorem mul (hP : HasAdjugateNormalForm A P) (f : R[X]) :
    HasAdjugateNormalForm A (f*P) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa only [add_mul] using hf.add hg
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, mul_assoc]
      apply HasAdjugateNormalForm.C_mul
      induction n with
      | zero => simpa using hP
      | succ n ih => simpa only [pow_succ', mul_assoc] using ih.X_mul

end HasAdjugateNormalForm

theorem normalForm_of_mem_cofactorIdeal (A : Matrix ι ι R) (P : R[X])
    (hP : P ∈ cofactorIdeal A) : HasAdjugateNormalForm A P := by
  let J : Ideal R[X] :=
    { carrier := {P | HasAdjugateNormalForm A P}
      zero_mem' := HasAdjugateNormalForm.zero
      add_mem' := fun h h' => h.add h'
      smul_mem' := fun f _ h => h.mul f }
  have hle : cofactorIdeal A ≤ J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨i,j⟩, rfl⟩
    change HasAdjugateNormalForm A ((pencilMatrix A).adjugate i j)
    refine ⟨Matrix.single j i 1, 0, ?_⟩
    simp [adjTrace, Matrix.map_single, Matrix.trace_single_mul]
  exact hle hP

end OuterVariableReduction

section DegreeNormalForm
variable {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}

theorem exists_multiplier_of_mem_cofactorIdeal
    (A : Matrix (Fin (k+1)) (Fin (k+1)) R) (P : R[X])
    (hP : P ∈ cofactorIdeal A) (hdeg : P.natDegree ≤ k) :
    ∃ Y : Matrix (Fin (k+1)) (Fin (k+1)) R, P = adjTrace A Y := by
  obtain ⟨Y,H,h⟩ := normalForm_of_mem_cofactorIdeal A P hP
  have hH : H = 0 := by
    by_contra hn
    have hF : (pencilMatrix A).det ≠ 0 := by
      intro hzero
      have := natDegree_det_pencilMatrix A
      simp only [hzero, natDegree_zero] at this
      omega
    have hd : (H*(pencilMatrix A).det).natDegree ≤ k := by
      have he : H*(pencilMatrix A).det = P - adjTrace A Y := by rw [h]; ring
      rw [he]
      exact le_trans (natDegree_sub_le _ _) (max_le hdeg (natDegree_adjTrace_le A Y))
    rw [natDegree_mul hn hF, natDegree_det_pencilMatrix] at hd
    omega
  refine ⟨Y, ?_⟩
  simpa only [hH, zero_mul, add_zero] using h
end DegreeNormalForm

section BivariateScaling
variable {K : Type*} [Field K] {k : ℕ}

theorem scaleHom_injective : Function.Injective (scaleHom (K := K)) := by
  apply (injective_iff_map_eq_zero _).2
  intro p hp
  have hc : p.comp (C X * X) = 0 := by
    apply Bivariate.swap.injective
    change Bivariate.swap (p.comp (C X * X)) = 0 at hp
    simpa only [map_zero] using hp
  rcases comp_eq_zero_iff.mp hc with h | ⟨_, h⟩
  · exact h
  · have hn := congrArg natDegree h
    rw [natDegree_C_mul_X X X_ne_zero, natDegree_C] at hn
    omega

theorem exists_constant_multiplier_of_mem_cofactorIdeal
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (P : K[X][X])
    (hP : P ∈ cofactorIdeal (pencilBase θ A))
    (houter : P.natDegree ≤ k) (htotal : (scaleHom P).natDegree ≤ k) :
    ∃ Y : Matrix (Fin (k+1)) (Fin (k+1)) K,
      P = adjTrace (pencilBase θ A) (Y.map C) := by
  obtain ⟨Y, hY⟩ := exists_multiplier_of_mem_cofactorIdeal _ _ hP houter
  have hs : (scaledTrace θ A Y).natDegree ≤ k := by
    simpa only [hY, scaleHom_adjTrace] using htotal
  obtain ⟨d, hd⟩ := (Set.finite_range (fun ij : Fin (k+1) × Fin (k+1) =>
    (Y ij.1 ij.2).natDegree)).bddAbove
  obtain ⟨Z, hZ⟩ := exists_constant_multiplier_of_bounded_scaledTrace θ hθ A Y d
    (fun i j => hd ⟨(i,j), rfl⟩) hs
  refine ⟨Z, scaleHom_injective ?_⟩
  rw [hY, scaleHom_adjTrace, scaleHom_adjTrace]
  exact hZ.symm

theorem adjugate_generation
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (P : K[X][X])
    (hP : P ∈ cofactorIdeal (pencilBase θ A)) (hdeg : TotalDegreeLE P k) :
    ∃ Y : Matrix (Fin (k+1)) (Fin (k+1)) K,
      P = adjTrace (pencilBase θ A) (Y.map C) :=
  exists_constant_multiplier_of_mem_cofactorIdeal θ hθ A P hP hdeg.outer hdeg.scaled

theorem coeff_adjTrace_eq_zero
    (θ : Fin (k+1) → K) (A Y : Matrix (Fin (k+1)) (Fin (k+1)) K) (q : ℕ)
    (hcrit : ∀ i j, (((pencilMatrix (pencilBase θ A)).adjugate i j).coeff q).coeff q = 0) :
    ((adjTrace (pencilBase θ A) (Y.map C)).coeff q).coeff q = 0 := by
  simp only [adjTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply, finsetSum_coeff, coeff_C_mul, hcrit, mul_zero,
    Finset.sum_const_zero]

theorem critical_ideal_eq_zero
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (q : ℕ) (hq : 3*q ≤ k)
    (hcrit : ∀ i j, (((pencilMatrix (pencilBase θ A)).adjugate i j).coeff q).coeff q = 0)
    {P : K[X][X]} (hP : P ∈ cofactorIdeal (pencilBase θ A))
    (hdeg : TotalDegreeLE P q) : P = 0 := by
  ext a b
  simp only [coeff_zero]
  by_cases hab : a+b ≤ q
  · have ha : a ≤ q := by omega
    have hb : b ≤ q := by omega
    let W : K[X][X] := monomial (q-a) (monomial (q-b) 1)
    have hW : TotalDegreeLE (W*P) k :=
      ((totalDegreeLE_monomial (q-a) (q-b) (1 : K)).mul hdeg).mono (by omega)
    have hWP : W*P ∈ cofactorIdeal (pencilBase θ A) :=
      Ideal.mul_mem_left _ W hP
    obtain ⟨Y, hY⟩ := adjugate_generation θ hθ A (W*P) hWP hW
    have hz : (((W*P).coeff q).coeff q) = 0 := by
      rw [hY]
      exact coeff_adjTrace_eq_zero θ A Y q hcrit
    have hca := coeff_monomial_mul P (q-a) a (monomial (q-b) (1 : K))
    have hcb := coeff_monomial_mul (P.coeff a) (q-b) b (1 : K)
    rw [Nat.add_sub_of_le ha] at hca
    rw [Nat.add_sub_of_le hb, one_mul] at hcb
    change (((monomial (q-a) (monomial (q-b) 1) * P).coeff q).coeff q) = 0 at hz
    rw [hca, hcb] at hz
    exact hz
  · exact hdeg a b (by omega)

theorem card_planeIndex (q : ℕ) : Fintype.card (PlaneIndex q) = (q+2).choose 2 := by
  rw [Fintype.card_subtype]
  simpa only [Fintype.card_fin] using (Fintype.card_product_filter_lt (α := Fin (q+2)))

theorem critical_cofactor_length
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (q : ℕ) (hq : 3*q ≤ k)
    (hcrit : ∀ i j, (((pencilMatrix (pencilBase θ A)).adjugate i j).coeff q).coeff q = 0) :
    ((q+2).choose 2 : ℕ∞) ≤ Module.length K (K[X][X] ⧸ cofactorIdeal (pencilBase θ A)) := by
  classical
  let I := cofactorIdeal (pencilBase θ A)
  let f : (PlaneIndex q → K) →ₗ[K] (K[X][X] ⧸ I) :=
    (Ideal.Quotient.mkₐ K I).toLinearMap.comp (planeMap q)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro P hP
    have hmem : planeMap q P ∈ cofactorIdeal (pencilBase θ A) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hP
    have hz := critical_ideal_eq_zero θ hθ A q hq hcrit hmem (totalDegreeLE_planeMap q P)
    funext i
    have hc := congrArg (fun p : K[X][X] => (p.coeff i.val.1.val).coeff
      (i.val.2.val-i.val.1.val-1)) hz
    simpa only [coeff_planeMap, coeff_zero, Pi.zero_apply] using hc
  have h := Module.length_le_of_injective (R := K) f hf
  rw [Module.length_eq_finrank, Module.finrank_fintype_fun_eq_card, card_planeIndex] at h
  exact h

theorem TotalDegreeLE.add {P Q : K[X][X]} {d : ℕ}
    (hP : TotalDegreeLE P d) (hQ : TotalDegreeLE Q d) : TotalDegreeLE (P+Q) d := by
  intro i j hij
  simp only [coeff_add, hP i j hij, hQ i j hij, add_zero]

end BivariateScaling

end PermanentBorder.AdjugateAlgebra

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.RowIdeals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial
section RowLength
variable {K : Type*} [Field K] {k : ℕ}

theorem finite_row_quotient
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Module.Finite K (K[X][X] ⧸ rowIdeal (pencilBase θ A)) := by
  classical
  let g := fun i : PlaneIndex (k-1) =>
    (Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A)))
      (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1))
  have hg := row_quotient_spanned θ hθ A hk
  change Submodule.span K (Set.range g) = ⊤ at hg
  exact Module.Finite.of_fg_top (Submodule.fg_def.mpr ⟨Set.range g, Set.finite_range g, hg⟩)

theorem row_quotient_finrank (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Module.finrank K (K[X][X] ⧸ rowIdeal (pencilBase θ A)) = (k+1).choose 2 := by
  classical
  let I := rowIdeal (pencilBase θ A)
  let f : (PlaneIndex (k-1) → K) →ₗ[K] (K[X][X] ⧸ I) :=
    (Ideal.Quotient.mkₐ K I).toLinearMap.comp (planeMap (k-1))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hmem : planeMap (k-1) v ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hv
    have hz := rowIdeal_low_degree_zero θ hθ A hk hmem (totalDegreeLE_planeMap (k-1) v)
    funext i
    have hc := congrArg (fun p : K[X][X] => (p.coeff i.val.1.val).coeff
      (i.val.2.val-i.val.1.val-1)) hz
    simpa only [coeff_planeMap, coeff_zero, Pi.zero_apply] using hc
  have := finite_row_quotient θ hθ A hk
  apply le_antisymm
  · have h := finrank_le_of_span_eq_top (row_quotient_spanned θ hθ A hk)
    simpa only [card_planeIndex, show k-1+2 = k+1 by omega] using h
  · have h := LinearMap.finrank_le_finrank_of_injective hf
    rw [Module.finrank_fintype_fun_eq_card, card_planeIndex] at h
    simpa only [show k-1+2 = k+1 by omega] using h
end RowLength
end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial
section RowRecovery
variable {K : Type*} [Field K] {k : ℕ}

theorem rowContraction_single (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i : Fin (k+1)) :
    rowContraction θ A (Pi.single i 1) = rowEntry (pencilBase θ A) i := by
  classical
  simp [rowContraction, rowPair_eq_sum, Pi.single_apply]

theorem rowEntry_top (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i : Fin (k+1)) :
    (scaleHom (rowEntry (pencilBase θ A) i)).coeff k =
      slopeTrace θ (Pi.single i 1) := by
  rw [← rowContraction_single, rowContraction_top]

theorem rowPair_neg {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (v : ι → R) : rowPair A (-v) = -rowPair A v := by
  simp only [rowPair_eq_sum, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

end RowRecovery
end PermanentBorder.AdjugateAlgebra

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

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Conductor
section
variable {K : Type*} [Field K] [Infinite K] {k : ℕ}

theorem charmatrix_neg_eq_pencil {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι R) : (-B).charmatrix = pencilMatrix B := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;>
    simp [pencilMatrix, h]

theorem cofactorIdeal_eq_matrixEntryIdeal {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (B : Matrix ι ι R) :
    cofactorIdeal B = matrixEntryIdeal (-B).charmatrix.adjugate := by
  rw [charmatrix_neg_eq_pencil]
  rfl

theorem critical_normalization_defect
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (q : ℕ) (hq : 3*q ≤ k)
    (hcrit : ∀ i j, (((pencilMatrix (pencilBase θ A)).adjugate i j).coeff q).coeff q = 0) :
    let T := -(pencilBase θ A)
    let Q := FractionRing K[X]
    let R := integralClosure K[X] (AdjoinRoot (T.charpoly.map (algebraMap K[X] Q)))
    ((q+2).choose 2 : ℕ∞) ≤ Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toLinearMap) := by
  let T := -(pencilBase θ A)
  have hs : (T.charpoly.map (algebraMap K[X] (FractionRing K[X]))).Separable :=
    PencilSeparability.distinct_slope_pencil_separable θ hθ A
  have h := critical_cofactor_length θ hθ A q hq hcrit
  rw [cofactorIdeal_eq_matrixEntryIdeal] at h
  have he := (polynomialCofactorQuotientEquiv (K := K) T).length_eq
  rw [← he] at h
  exact h.trans (normalization_adjugate_length_global (K := K) T hs)

end
end PermanentBorder.AdjugateAlgebra

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Gradients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.GradientAlgebra

open Finset

section CharacteristicTwo
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CharP R 2]

theorem permanent_eq_det (M : Matrix ι ι R) : M.permanent = M.det := by
  rw [Matrix.permanent, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp [h, CharTwo.neg_eq]
end CharacteristicTwo

section Derivative
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [DecidableEq ι]

theorem derivation_prod (D : Derivation R A A) (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih]
    simp only [smul_eq_mul, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := by
      intro h
      exact ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hai, Finset.prod_insert]
    · ring
    · exact Finset.notMem_mono (Finset.erase_subset _ _) ha

variable [Fintype ι]

theorem derivation_det_updateCol (D : Derivation R A A) (M : Matrix ι ι A) :
    D M.det = ∑ j, (M.updateCol j (fun i => D (M i j))).det := by
  rw [Matrix.det_apply, map_sum]
  simp only [Units.smul_def, map_zsmul, derivation_prod]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def]
  congr 1
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  rw [Matrix.updateCol_self]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact (Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)).symm

theorem derivation_det (D : Derivation R A A) (M : Matrix ι ι A) :
    D M.det = ∑ j, ∑ i, M.adjugate j i * D (M i j) := by
  rw [derivation_det_updateCol]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl
end Derivative

section AffinePencil
open MvPolynomial
variable {R σ : Type*} [CommRing R]

theorem biCoefficientPart_pderiv (a b : ℕ)
    (P : MvPolynomial σ (Polynomial (Polynomial R))) (i : σ) :
    biCoefficientPart a b (pderiv i P) = pderiv i (biCoefficientPart a b P) := by
  ext d
  simp only [coeff_biCoefficientPart, coeff_pderiv]
  simp only [← Nat.cast_add_one, Polynomial.coeff_mul_natCast]

theorem eval_biCoefficientPart (a b : ℕ) (x : σ → R)
    (P : MvPolynomial σ (Polynomial (Polynomial R))) :
    eval x (biCoefficientPart a b P) =
      ((eval (fun i => Polynomial.C (Polynomial.C (x i))) P).coeff a).coeff b := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial d c =>
    simp only [biCoefficientPart_monomial, eval_monomial]
    have hp : d.prod (fun i n => (Polynomial.C (Polynomial.C (x i))) ^ n) =
        Polynomial.C (Polynomial.C (d.prod (fun i n => x i ^ n))) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [hp, mul_comm c, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, mul_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pderiv_det_genericAffinePencil (θ : ι → R) (a b : ι) :
    pderiv (a,b) (genericAffinePencil θ).det = (genericAffinePencil θ).adjugate b a := by
  classical
  have hd := derivation_det (pderiv (a,b)) (genericAffinePencil θ)
  rw [hd]
  simp only [pderiv_genericAffinePencil, Prod.mk.injEq]
  rw [Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro i _
    simp [Ne.symm hj]
  · simp

theorem eval_genericAffinePencil (θ : ι → R) (x : Matrix ι ι R) :
    (eval (fun ij : ι × ι => Polynomial.C (Polynomial.C (x ij.1 ij.2)))).mapMatrix
      (genericAffinePencil θ) = fixedAffinePencil θ x := by
  ext i j
  simp [genericAffinePencil, fixedAffinePencil]

theorem gradient_affineSelector [CharP R 2] (θ : ι → R)
    (x : Matrix ι ι R) (q : ℕ) (a b : ι) :
    eval (fun ij : ι × ι => x ij.1 ij.2) (pderiv (a,b) (affineSelector θ q)) =
      (((fixedAffinePencil θ x).adjugate b a).coeff q).coeff q := by
  classical
  have hp := permanent_eq_det (genericAffinePencil θ)
  rw [affineSelector, hp, ← biCoefficientPart_pderiv,
    pderiv_det_genericAffinePencil, eval_biCoefficientPart]
  have h := congrArg (fun M : Matrix ι ι (Polynomial (Polynomial R)) => M b a)
    ((eval (fun ij : ι × ι => Polynomial.C (Polynomial.C (x ij.1 ij.2)))).map_adjugate
      (genericAffinePencil θ))
  change eval (fun ij : ι × ι => Polynomial.C (Polynomial.C (x ij.1 ij.2)))
    ((genericAffinePencil θ).adjugate b a) = _ at h
  rw [h, eval_genericAffinePencil]
end AffinePencil

end PermanentBorder.GradientAlgebra

namespace PermanentBorder.Selector
open MvPolynomial
section
variable {R σ : Type*} [CommRing R]

lemma bivariateToNested_coeff (P : MvPolynomial (Fin 2) R) (q : ℕ) :
    ((bivariateToNested P).coeff q).coeff q = P.coeff (countIndex q) := by
  change ((Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom
    (finSuccEquiv R 1 P)).coeff q).coeff q = _
  rw [Polynomial.coeff_map]
  change ((uniqueAlgEquiv R (Fin 1)) ((finSuccEquiv R 1 P).coeff q)).coeff q = _
  rw [coeff_uniqueAlgEquiv, finSuccEquiv_coeff_coeff]
  congr 1
  ext i
  fin_cases i
  · simp [countIndex]
  · change (Finsupp.cons q (Finsupp.single (0 : Fin 1) q))
      (Fin.succ (0 : Fin 1)) = q
    change (Finsupp.single (0 : Fin 1) q) 0 = q
    simp

lemma commAlgEquiv_coeff_coeff (P : MvPolynomial (Fin 2) (MvPolynomial σ R))
    (a : Fin 2 →₀ ℕ) (b : σ →₀ ℕ) :
    ((commAlgEquiv R (Fin 2) σ P).coeff b).coeff a = (P.coeff a).coeff b := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP,hQ]
  | monomial d c =>
    induction c using MvPolynomial.induction_on' with
    | add c e hc he => simp [map_add, hc,he]
    | monomial e c =>
      change ((AddMonoidAlgebra.commAlgEquiv R
        (AddMonoidAlgebra.single d (AddMonoidAlgebra.single e c))).coeff b).coeff a = _
      rw [AddMonoidAlgebra.commAlgEquiv_single_single]
      change ((monomial e (monomial d c)).coeff b).coeff a = _
      simp only [coeff_monomial]
      split_ifs <;> simp_all

lemma biCoefficientPart_interchange (P : MvPolynomial (Fin 2) (MvPolynomial σ R)) (q : ℕ) :
    GradientAlgebra.biCoefficientPart q q (interchangeBivariate P) = P.coeff (countIndex q) := by
  ext d
  rw [GradientAlgebra.coeff_biCoefficientPart]
  change (((map bivariateToNested (commAlgEquiv R (Fin 2) σ P)).coeff d).coeff q).coeff q = _
  rw [coeff_map,bivariateToNested_coeff,commAlgEquiv_coeff_coeff]

end

lemma diagonalCoefficient_eq_affineSelector {R I : Type*} [CommRing R]
    [Fintype I] [DecidableEq I] (θ : I → R) (q : ℕ) :
    diagonalCoefficient (Matrix.of fun i j => (X (i,j) : MvPolynomial (I×I) R))
      (fun i => C (θ i)) q = GradientAlgebra.affineSelector θ q := by
  classical
  unfold diagonalCoefficient GradientAlgebra.affineSelector
  rw [← biCoefficientPart_interchange]
  congr 1
  unfold Matrix.permanent
  simp only [map_sum,map_prod]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.prod_congr rfl
  intro i _
  simp only [Matrix.add_apply,Matrix.of_apply,Matrix.diagonal_apply,
    GradientAlgebra.genericAffinePencil]
  split_ifs
  · simp only [map_add,map_mul,interchangeBivariate_C_X,interchangeBivariate_X_zero,
      interchangeBivariate_C_C,interchangeBivariate_X_one]
    simp only [← map_mul,← map_add]
    rw [add_comm]
    congr 2
    rw [mul_comm]
  · simp
end PermanentBorder.Selector

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Centralizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial Polynomial Matrix
open GradientAlgebra AdjugateAlgebra Conductor

lemma fixedAffinePencil_eq_pencil {K : Type*} [Field K] {k : ℕ}
    (θ : Fin (k+1) → K) (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    fixedAffinePencil θ A = pencilMatrix (pencilBase θ A) := by
  ext i j
  simp only [fixedAffinePencil, pencilMatrix, pencilBase, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, Matrix.diagonal_apply,
    smul_eq_mul, map_add, map_mul]
  split_ifs <;> simp
  ring

theorem gradient_forces_normalization_defect {K : Type*}
    [Field K] [Infinite K] [CharP K 2] {k q : ℕ} (hq : 3*q ≤ k)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (hcrit : ∀ ij : Fin (k+1) × Fin (k+1), MvPolynomial.eval
      (fun ab : Fin (k+1) × Fin (k+1) => A ab.1 ab.2)
      (pderiv ij (diagonalCoefficient
        (Matrix.of fun a b => (MvPolynomial.X (a,b) :
          MvPolynomial (Fin (k+1) × Fin (k+1)) K)) (fun i => MvPolynomial.C (θ i)) q)) = 0) :
    let T := -(pencilBase θ A)
    let Q := FractionRing K[X]
    let R := integralClosure K[X] (AdjoinRoot (T.charpoly.map (algebraMap K[X] Q)))
    ((q+2).choose 2 : ℕ∞) ≤ Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toLinearMap) := by
  apply critical_normalization_defect θ hθ A q hq
  intro i j
  have h := hcrit (j,i)
  rw [diagonalCoefficient_eq_affineSelector, gradient_affineSelector,
    fixedAffinePencil_eq_pencil] at h
  exact h

end PermanentBorder.Selector

namespace PermanentBorder.CentralizerDimension

open Matrix MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem eval_coordinateMatrix (A : Matrix ι ι K) (B : centralizer A) :
    (coordinateMatrix A).map (eval (fun b => (centralizerBasis A).repr B b)) = B.val := by
  classical
  ext i j
  have h := congrArg (fun W : centralizer A => W.val i j)
    ((centralizerBasis A).sum_repr B)
  simp only [coordinateMatrix, Matrix.map_apply, map_sum, map_mul, eval_C, eval_X]
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_comm] using h

theorem eval_determinantPolynomial (A : Matrix ι ι K) (B : centralizer A) :
    eval (fun b => (centralizerBasis A).repr B b) (determinantPolynomial A) =
      B.val.det := by
  rw [determinantPolynomial, RingHom.map_det]
  change ((coordinateMatrix A).map (eval (fun b => (centralizerBasis A).repr B b))).det = _
  rw [eval_coordinateMatrix]

theorem determinantPolynomial_ne_zero (A : Matrix ι ι K) :
    determinantPolynomial A ≠ 0 := by
  intro h
  have he := eval_determinantPolynomial A (centralizerOne A)
  simp [h, centralizerOne] at he

end PermanentBorder.CentralizerDimension

namespace PermanentBorder.CoordinateGauge
open Module Submodule
variable {K ι : Type*} [Field K] [Fintype ι]

theorem exists_coordinate_gauge (S : Submodule K (ι → K)) :
    ∃ a : Fin (Module.finrank K S) → ι, Function.Injective a ∧
      Function.Bijective (fun x : S => fun j => x.val (a j)) := by
  classical
  let q (i : ι) : Module.Dual K S := (LinearMap.proj i).comp S.subtype
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K q
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let r : S →ₗ[K] (κ → K) := LinearMap.pi fun j => q (a j)
  have hri : Function.Injective r := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hz : ∀ j, q (a j) x = 0 := congrFun (show r x = 0 from hx)
    have hs : ∀ g ∈ Submodule.span K (Set.range (q ∘ a)), g x = 0 := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem z hz' => obtain ⟨j, rfl⟩ := hz'; exact hz j
      | zero => rfl
      | add y z _ _ hy hz => simp only [LinearMap.add_apply, hy, hz, add_zero]
      | smul c y _ hy => simp only [LinearMap.smul_apply, hy, smul_zero]
    have hcoord (i : ι) : q i x = 0 := by
      apply hs
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self i)
    change x = 0
    apply Subtype.ext
    funext i
    exact hcoord i
  have hc : Fintype.card κ = Module.finrank K S := by
    apply Nat.le_antisymm
    · simpa only [Subspace.dual_finrank_eq] using hli.fintype_card_le_finrank
    · simpa only [Module.finrank_fintype_fun_eq_card] using
        (LinearMap.finrank_le_finrank_of_injective hri)
  have hrs : Function.Surjective r :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa only [Module.finrank_fintype_fun_eq_card] using hc.symm)).mp hri
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨a ∘ e.symm, ha.comp e.symm.injective, ?_, ?_⟩
  · intro x y h
    apply hri
    funext j
    have he := congrFun h (e j)
    change x.val (a j) = y.val (a j)
    simpa only [Function.comp_apply, e.symm_apply_apply] using he
  · intro v
    obtain ⟨x, hx⟩ := hrs (v ∘ e)
    refine ⟨x, ?_⟩
    funext j
    have he := congrFun hx (e.symm j)
    simpa only [r, LinearMap.pi_apply, q, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.proj_apply, Function.comp_apply, e.apply_symm_apply] using he

end PermanentBorder.CoordinateGauge

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.CoordinateFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CoordinateNormalization
open Matrix MvPolynomial CoordinateGauge
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Infinite K]
  [Fintype ι] [DecidableEq ι]

theorem exists_base_eval_ne_zero {κ : Type*} (p : MvPolynomial κ L) (hp : p ≠ 0) :
    ∃ x : κ → K, MvPolynomial.eval (algebraMap K L ∘ x) p ≠ 0 := by
  classical
  by_contra! h
  apply hp
  apply MvPolynomial.funext_set (fun _ => Set.range (algebraMap K L))
    (fun _ => Set.infinite_range_of_injective (algebraMap K L).injective)
  intro x hx
  choose y hy using fun i => hx i (Set.mem_univ i)
  have he : algebraMap K L ∘ y = x := funext hy
  simp only [← he, h, map_zero]

theorem eval_basisDeterminant {κ : Type*} [Fintype κ]
    (S : Submodule L ((ι × ι) → L)) (b : Module.Basis κ L S) (v : S) :
    MvPolynomial.eval (fun a => b.repr v a) (basisDeterminant S b) =
      Matrix.det (Function.curry v.val) := by
  classical
  unfold basisDeterminant
  rw [RingHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.eval (fun a => b.repr v a)
    (∑ a, C ((b a).val (i,j)) * X a) = v.val (i,j)
  simp only [map_sum, map_mul, eval_C, eval_X]
  have h := congrArg (fun z : S => z.val (i,j)) (b.sum_repr v)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm] using h

theorem exists_invertible_coordinate_gauge
    (S : Submodule L ((ι × ι) → L))
    (hS : ∃ v : S, Matrix.det (Function.curry v.val) ≠ 0) :
    ∃ (a : Fin (Module.finrank L S) → ι × ι) (v : S),
      Function.Injective a ∧ Matrix.det (Function.curry v.val) ≠ 0 ∧
      ∀ j, ∃ c : K, v.val (a j) = algebraMap K L c := by
  classical
  obtain ⟨a, hai, hab⟩ := exists_coordinate_gauge S
  let r : S →ₗ[L] (Fin (Module.finrank L S) → L) :=
    LinearMap.pi fun j => (LinearMap.proj (a j)).comp S.subtype
  let e : S ≃ₗ[L] (Fin (Module.finrank L S) → L) := LinearEquiv.ofBijective r hab
  let b := Module.Basis.ofEquivFun e
  have hp : basisDeterminant S b ≠ 0 := by
    obtain ⟨v, hv⟩ := hS
    intro h
    apply hv
    rw [← eval_basisDeterminant S b v, h, map_zero]
  obtain ⟨x, hx⟩ := exists_base_eval_ne_zero (K := K) (basisDeterminant S b) hp
  let v := e.symm (algebraMap K L ∘ x)
  have hre : (fun j => b.repr v j) = algebraMap K L ∘ x := by
    funext j
    simp only [b, Module.Basis.ofEquivFun_repr_apply, v, LinearEquiv.apply_symm_apply]
  refine ⟨a, v, hai, ?_, ?_⟩
  · rwa [← hre, eval_basisDeterminant] at hx
  · intro j
    refine ⟨x j, ?_⟩
    have h := congrFun (e.apply_symm_apply (algebraMap K L ∘ x)) j
    exact h

end PermanentBorder.CoordinateNormalization

namespace PermanentBorder.OrbitNormalization
open Matrix CentralizerDimension CentralizerBaseChange CoordinateNormalization
variable {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]

variable {K : Type*} [Field K] [Algebra K L] [Infinite K]

theorem exists_normalized_intertwiner (A : Matrix ι ι L) (C : Matrix ι ι K)
    (P : (Matrix ι ι L)ˣ)
    (hP : A * (P : Matrix ι ι L) = (P : Matrix ι ι L) * C.map (algebraMap K L)) :
    ∃ (a : Fin (Module.finrank K (centralizer C)) → ι × ι)
      (Q : (Matrix ι ι L)ˣ),
      Function.Injective a ∧
      A * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * C.map (algebraMap K L) ∧
      ∀ j, ∃ c : K, (Q : Matrix ι ι L) (a j).1 (a j).2 = algebraMap K L c := by
  classical
  let S := intertwinerSpace A (C.map (algebraMap K L))
  have hd : Module.finrank L S = Module.finrank K (centralizer C) :=
    (intertwinerEquivCentralizer A _ P hP).finrank_eq.symm.trans
      (finrank_centralizer_map C)
  have hS : ∃ v : S, Matrix.det (Function.curry v.val) ≠ 0 := by
    refine ⟨⟨Function.uncurry (P : Matrix ι ι L), hP⟩, ?_⟩
    exact (Matrix.isUnits_det_units P).ne_zero
  obtain ⟨a, v, hai, hv, hvK⟩ := exists_invertible_coordinate_gauge (K := K) S hS
  obtain ⟨Q, hQ⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)
  let e := finCongr hd
  refine ⟨a ∘ e.symm, Q, hai.comp e.symm.injective, ?_, ?_⟩
  · rw [hQ]
    exact v.property
  · intro j
    obtain ⟨c, hc⟩ := hvK (e.symm j)
    exact ⟨c, by simpa only [hQ, Function.comp_apply, Function.curry] using hc⟩

end PermanentBorder.OrbitNormalization

namespace PermanentBorder.CentralizerParameters
open Matrix MvPolynomial CentralizerDimension CentralizerBaseChange
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

theorem entry_expansion (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) (i j : ι) :
    B.val i j = ∑ a, coefficients C B a * algebraMap K L ((centralizerBasis C a).val i j) := by
  have h := congrArg (fun D : centralizer (C.map (algebraMap K L)) => D.val i j)
    ((centralizerBasisMap C (centralizerBasis C)).sum_repr B)
  simpa only [coefficients, Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, centralizerBasisMap_apply,
    mapCentralizer, Matrix.map_apply] using h.symm

theorem eval_determinant (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) :
    MvPolynomial.aeval (coefficients C B) (determinantPolynomial C) = B.val.det := by
  rw [determinantPolynomial, AlgHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.aeval (coefficients C B)
    (∑ a, MvPolynomial.C ((centralizerBasis C a).val i j) * X a) = B.val i j
  simp only [map_sum, map_mul, aeval_C, aeval_X]
  rw [entry_expansion C B i j]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem determinant_relation (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) (hB : B.val.det = 0) :
    determinantPolynomial C ≠ 0 ∧
      MvPolynomial.aeval (coefficients C B) (determinantPolynomial C) = 0 :=
  ⟨determinantPolynomial_ne_zero C, (eval_determinant C B).trans hB⟩

end PermanentBorder.CentralizerParameters

namespace PermanentBorder.MatrixSubfield
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mul_mem (F : IntermediateField K L) (A B : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (hB : ∀ i j, B i j ∈ F) :
    ∀ i j, (A * B) i j ∈ F := by
  intro i j
  exact F.sum_mem fun k _ => F.mul_mem (hA i k) (hB k j)

theorem unit_inv_mem (F : IntermediateField K L) (P : (Matrix ι ι L)ˣ)
    (hP : ∀ i j, (P : Matrix ι ι L) i j ∈ F) :
    ∀ i j, (↑P⁻¹ : Matrix ι ι L) i j ∈ F := by
  let A : Matrix ι ι F := fun i j => ⟨(P : Matrix ι ι L) i j, hP i j⟩
  have hA : A.map (algebraMap F L) = (P : Matrix ι ι L) := rfl
  have hd : A.det ≠ 0 := by
    intro h
    have he : algebraMap F L A.det = (P : Matrix ι ι L).det :=
      (algebraMap F L).map_det A
    rw [h, map_zero] at he
    exact (Matrix.isUnits_det_units P).ne_zero he.symm
  have hi := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F L))
    (Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hd))
  simp only [Matrix.map_mul, hA, Matrix.map_one _ (map_zero _) (map_one _)] at hi
  have he : A⁻¹.map (algebraMap F L) = (↑P⁻¹ : Matrix ι ι L) := by
    calc
      _ = (A⁻¹.map (algebraMap F L) * (P : Matrix ι ι L)) * (↑P⁻¹ : Matrix ι ι L) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [hi, one_mul]
  intro i j
  rw [← he]
  exact ((A⁻¹) i j).property

end PermanentBorder.MatrixSubfield

namespace PermanentBorder.ParameterBounds
open Algebra MvPolynomial
universe u
variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_lt_of_relation_fintype {L : Type u} [Field L] [Algebra K L]
    {κ : Type*} [Fintype κ] (x : κ → L) (p : MvPolynomial κ K) (hp : p ≠ 0)
    (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) < (Fintype.card κ : Cardinal) := by
  classical
  let e := Fintype.equivFin κ
  let y := x ∘ e.symm
  have hy : Set.range y = Set.range x := e.symm.surjective.range_comp x
  rw [← hy]
  apply field_adjoin_trdeg_lt_of_relation y (MvPolynomial.rename e p)
  · exact fun h => hp ((MvPolynomial.rename_injective e e.injective) (by simpa using h))
  · simpa only [MvPolynomial.aeval_rename, y, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id] using hx

end PermanentBorder.ParameterBounds

namespace PermanentBorder.CommutingPairs
open Matrix CentralizerDimension CentralizerParameters OrbitNormalization
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem normalized_pair_field_bound {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin n) (Fin n) K)
    (P : (Matrix (Fin n) (Fin n) L)ˣ)
    (hP : A * (P : Matrix (Fin n) (Fin n) L) =
      (P : Matrix (Fin n) (Fin n) L) * C.map (algebraMap K L))
    (hAB : A * B = B * A) (hB : B.det = 0) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F < (n * n : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) := by
  classical
  obtain ⟨a, Q, hai, hQ, hQa⟩ := exists_normalized_intertwiner A C P hP
  let j := Module.finrank K (centralizer C)
  let C' := C.map (algebraMap K L)
  have hC' : C' = (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * A * (Q : Matrix (Fin n) (Fin n) L) := by
    calc
      _ = (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * ((Q : Matrix (Fin n) (Fin n) L) * C') := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [← hQ, mul_assoc]
  let B' : centralizer C' := ⟨(↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * B * (Q : Matrix (Fin n) (Fin n) L), by
    change C' * _ = _ * C'
    rw [hC']
    simp only [mul_assoc]
    simp only [← mul_assoc (Q : Matrix (Fin n) (Fin n) L), Units.mul_inv, one_mul]
    simp only [← mul_assoc]
    rw [mul_assoc (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) A B, hAB, ← mul_assoc]⟩
  let κ := {p : Fin n × Fin n // p ∉ Set.range a} ⊕ Fin j
  let x : κ → L := Sum.elim
    (fun p => (Q : Matrix (Fin n) (Fin n) L) p.val.1 p.val.2)
    (coefficients C B')
  let F := IntermediateField.adjoin K (Set.range x)
  have hx (i : κ) : x i ∈ F := IntermediateField.subset_adjoin K _ (Set.mem_range_self i)
  have ha_card : Fintype.card {p : Fin n × Fin n // p ∈ Set.range a} = j := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (Equiv.ofInjective a hai)).symm
  have hj : j ≤ n * n := by
    simpa only [Fintype.card_fin, Fintype.card_prod] using Fintype.card_le_of_injective a hai
  have hκ : Fintype.card κ = n * n := by
    simp only [κ, Fintype.card_sum, Fintype.card_subtype_compl, ha_card,
      Fintype.card_prod, Fintype.card_fin]
    exact Nat.sub_add_cancel hj
  have hB' : B'.val.det = 0 := (Matrix.det_units_conj' Q B).trans hB
  obtain ⟨hp, hxp⟩ := determinant_relation C B' hB'
  have hFp : Algebra.trdeg K F < (Fintype.card κ : Cardinal) := by
    apply ParameterBounds.field_adjoin_trdeg_lt_of_relation_fintype x
      (MvPolynomial.rename (Sum.inr : Fin j → κ) (determinantPolynomial C))
    · exact fun h => hp ((MvPolynomial.rename_injective _ Sum.inr_injective) (by simpa using h))
    · simpa only [MvPolynomial.aeval_rename, Function.comp_def, x, Sum.elim_inr] using hxp
  have hQF : ∀ i j, (Q : Matrix (Fin n) (Fin n) L) i j ∈ F := by
    intro i j
    by_cases h : (i,j) ∈ Set.range a
    · obtain ⟨b, hb⟩ := h
      obtain ⟨c, hc⟩ := hQa b
      rw [hb] at hc
      rw [hc]
      exact F.algebraMap_mem c
    · exact hx (Sum.inl ⟨(i,j), h⟩)
  have hQiF := MatrixSubfield.unit_inv_mem F Q hQF
  have hCF : ∀ i j, C' i j ∈ F := fun i j => F.algebraMap_mem (C i j)
  have hBF : ∀ i j, B'.val i j ∈ F := by
    intro i j
    rw [entry_expansion C B' i j]
    exact F.sum_mem fun b _ => F.mul_mem (hx (Sum.inr b)) (F.algebraMap_mem _)
  have hAeq : A = (Q : Matrix (Fin n) (Fin n) L) * C' * (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) := by
    rw [← hQ, mul_assoc, Units.mul_inv, mul_one]
  have hBeq : B = (Q : Matrix (Fin n) (Fin n) L) * B'.val * (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) := by
    change B = (Q : Matrix (Fin n) (Fin n) L) *
      ((↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * B * (Q : Matrix (Fin n) (Fin n) L)) *
      (↑Q⁻¹ : Matrix (Fin n) (Fin n) L)
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [hκ] using hFp
  · rw [hAeq]
    exact MatrixSubfield.mul_mem F _ _ (MatrixSubfield.mul_mem F _ _ hQF hCF) hQiF
  · rw [hBeq]
    exact MatrixSubfield.mul_mem F _ _ (MatrixSubfield.mul_mem F _ _ hQF hBF) hQiF

end PermanentBorder.CommutingPairs

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Nilpotents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.NilpotentOrbits
open scoped DirectSum
open Submodule Module Polynomial Ideal Submodule.IsPrincipal Submodule.Quotient

section Decomposition
variable {R M : Type*} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
  [AddCommGroup M] [Module R M]

/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin

The following decomposition theorem is adapted from Mathlib.Algebra.Module.PID.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Module/PID.lean

This code has been modified.
-/

theorem decomposition_of_generators {p : R} (hp : Irreducible p)
    (hM : Module.IsTorsion' M (Submonoid.powers p))
    (d : ℕ) (s : Fin d → M) (hs : Submodule.span R (Set.range s) = ⊤) :
    ∃ k : Fin d → ℕ, Nonempty (M ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ k i) := by
  classical
  induction d generalizing M with
  | zero =>
    use finZeroElim
    rw [Set.range_eq_empty, Submodule.span_empty] at hs
    have : Unique M :=
      ⟨⟨0⟩, fun x => by dsimp; rw [← Submodule.mem_bot R, hs]; exact Submodule.mem_top⟩
    exact ⟨0⟩
  | succ d IH =>
    have : ∀ x : M, Decidable (x = 0) := fun _ => by classical infer_instance
    obtain ⟨j, hj⟩ := exists_isTorsionBy hM d.succ d.succ_ne_zero s hs
    let s' : Fin d → M ⧸ R ∙ s j := Submodule.Quotient.mk ∘ s ∘ j.succAbove

    have := IH ?_ s' ?_
    · obtain ⟨k, ⟨f⟩⟩ := this
      clear IH
      have : ∀ i : Fin d,
          ∃ x : M, p ^ k i • x = 0 ∧ f (Submodule.Quotient.mk x) = DirectSum.lof R _ _ i 1 := by
        intro i
        let fi := f.symm.toLinearMap.comp (DirectSum.lof _ _ _ i)
        obtain ⟨x, h0, h1⟩ := exists_smul_eq_zero_and_mk_eq hp hM hj fi; refine ⟨x, h0, ?_⟩; rw [h1]
        simp only [fi, LinearMap.coe_comp, f.symm.coe_toLinearMap, f.apply_symm_apply,
          Function.comp_apply]
      refine ⟨?_, ⟨?_⟩⟩
      · exact fun a => (fun i => (Option.rec (pOrder hM (s j)) k i : ℕ)) (finSuccEquiv d a)
      · refine
          (lequivProdOfRightSplitExact
            (g := f.toLinearMap.comp <| mkQ _)
            (f := (DirectSum.toModule _ _ _ fun i => (liftQSpanSingleton (p ^ k i)
                (LinearMap.toSpanSingleton _ _ _)
                (show (LinearMap.toSpanSingleton R M (this i).choose) (p ^ k i) = 0 from
                  (this i).choose_spec.left) : R ⧸ _ →ₗ[R] _)))
              (R ∙ s j).injective_subtype ?_ ?_).symm ≪≫ₗ
          (((quotTorsionOfEquivSpanSingleton R M (s j)).symm ≪≫ₗ
            (quotEquivOfEq (torsionOf R M (s j)) _
              (Ideal.torsionOf_eq_span_pow_pOrder hp hM (s j)))).prodCongr (.refl _ _)) ≪≫ₗ
          (@DirectSum.lequivProdDirectSum R _ _
            (fun i => R ⧸ R ∙ p ^ @Option.rec _ (fun _ => ℕ) (pOrder hM <| s j) k i) _ _).symm ≪≫ₗ
          (DirectSum.lequivCongrLeft R (finSuccEquiv d).symm)
        · rw [range_subtype, LinearEquiv.ker_comp, ker_mkQ]
        · rw [LinearMap.comp_assoc]
          ext i : 3
          simp only [LinearMap.coe_comp, Function.comp_apply, mkQ_apply]
          rw [LinearEquiv.coe_toLinearMap, LinearMap.id_apply, DirectSum.toModule_lof,
            liftQSpanSingleton_apply, LinearMap.toSpanSingleton_apply_one, Ideal.Quotient.mk_eq_mk,
            map_one (Ideal.Quotient.mk _), (this i).choose_spec.right]
    · exact (mk_surjective _).forall.mpr fun x =>
        ⟨(@hM x).choose, by rw [← Quotient.mk_smul, (@hM x).choose_spec, Quotient.mk_zero]⟩
    · have hs' := congr_arg (Submodule.map <| mkQ <| R ∙ s j) hs
      rw [Submodule.map_span, Submodule.map_top, range_mkQ] at hs'
      simp only [s']; rw [← Function.comp_assoc, Set.range_comp (_ ∘ s), Fin.range_succAbove]
      rw [← Set.range_comp, ← Set.insert_image_compl_eq_range _ j, Function.comp_apply,
        mkQ_apply, (Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _),
        Submodule.span_insert_zero] at hs'
      exact hs'

end Decomposition

section Nilpotent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem torsion_of_nilpotent (f : Module.End K V) (hf : IsNilpotent f) :
    Module.IsTorsion' (Module.AEval' f) (Submonoid.powers (X : K[X])) := by
  obtain ⟨e, he⟩ := hf
  intro x
  refine ⟨⟨X ^ e, ⟨e, rfl⟩⟩, ?_⟩
  change (X ^ e : K[X]) • x = 0
  obtain ⟨v, rfl⟩ := (Module.AEval'.of f).surjective x
  rw [Module.AEval'.X_pow_smul_of, he, zero_smul, map_zero]

theorem nilpotent_decomposition {n : ℕ} (b : Module.Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ,
      Nonempty (Module.AEval' f ≃ₗ[K[X]] ⨁ i : Fin n, Block (K := K) (e i)) := by
  let b' := b.map (Module.AEval'.of f)
  exact decomposition_of_generators Polynomial.irreducible_X
    (torsion_of_nilpotent f hf) n b'
    (Submodule.span_eq_top_of_span_eq_top K K[X] _ b'.span_eq)

theorem unit_conjugacy_of_intertwiner (f g : Module.End K V)
    (L : V ≃ₗ[K] V) (hL : ∀ v, L (f v) = g (L v)) :
    ∃ U : (Module.End K V)ˣ, g = (U : Module.End K V) * f * (↑U⁻¹ : Module.End K V) := by
  let U := (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm L
  have hu : (U : Module.End K V) = L.toLinearMap := rfl
  have h : (U : Module.End K V) * f = g * (U : Module.End K V) := by
    ext v
    exact hL v
  refine ⟨U, ?_⟩
  rw [h, mul_assoc, Units.mul_inv, mul_one]

end Nilpotent

end PermanentBorder.NilpotentOrbits

namespace PermanentBorder.NilpotentBlocks
open Polynomial Module
open scoped DirectSum
variable {K : Type*} [Field K]

theorem X_smul_blockBasis (e : ℕ) (i : Fin e) :
    (X : K[X]) • blockBasis (K := K) e i =
      if h : i.val + 1 < e then blockBasis e ⟨i.val + 1, h⟩ else 0 := by
  rw [blockBasis_apply]
  change Ideal.Quotient.mk _ ((X : K[X]) * X ^ i.val) = _
  rw [← pow_succ']
  split_ifs with h
  · exact (blockBasis_apply e ⟨i.val + 1, h⟩).symm
  · have he : i.val + 1 = e := by omega
    rw [he]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)

@[simp] theorem action_sumBasis {n : ℕ} (e : Fin n → ℕ)
    (i : Fin n) (j : Fin (e i)) :
    action (K := K) e (sumBasis e ⟨i,j⟩) =
      if h : j.val + 1 < e i then sumBasis e ⟨i,⟨j.val + 1,h⟩⟩ else 0 := by
  classical
  rw [sumBasis_apply]
  change (X : K[X]) • DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i (blockBasis (e i) j) = _
  have hmap := (DirectSum.lof K[X] (Fin n) (fun i => Block (K := K) (e i)) i).map_smul
    (X : K[X]) (blockBasis (e i) j)
  change DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i ((X : K[X]) • blockBasis (e i) j) =
    (X : K[X]) • DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i
      (blockBasis (e i) j) at hmap
  rw [← hmap, X_smul_blockBasis]
  split_ifs with h
  · exact (sumBasis_apply e i ⟨j.val + 1,h⟩).symm
  · exact map_zero _

theorem toMatrix_action {n : ℕ} (e : Fin n → ℕ) :
    LinearMap.toMatrix (sumBasis (K := K) e) (sumBasis e) (action e) = shiftMatrix e := by
  classical
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [LinearMap.toMatrix_apply, action_sumBasis]
  split_ifs with h
  · simp only [Basis.repr_self, Finsupp.single_apply]
    by_cases hab : a = b
    · subst b
      simp [shiftMatrix, Fin.ext_iff, eq_comm]
    · have hba : b ≠ a := Ne.symm hab
      simp [shiftMatrix, hab, hba]
  · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    simp only [shiftMatrix]
    split_ifs with hab
    · obtain ⟨rfl, hij⟩ := hab
      omega
    · rfl

end PermanentBorder.NilpotentBlocks

namespace PermanentBorder.NilpotentBlocks
open Polynomial Module
open scoped DirectSum
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem toMatrix_of_intertwiner {W ι : Type*} [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K W) (f : Module.End K V)
    (g : Module.End K W) (L : V ≃ₗ[K] W) (hL : ∀ v, L (f v) = g (L v)) :
    LinearMap.toMatrix (b.map L.symm) (b.map L.symm) f = LinearMap.toMatrix b b g := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  apply LinearMap.ext
  intro x
  change L (f (L.symm x)) = g x
  rw [hL, L.apply_symm_apply]

theorem shift_basis_of_equiv {n : ℕ} (e : Fin n → ℕ) (f : Module.End K V)
    (L : V ≃ₗ[K] ⨁ i : Fin n, Block (K := K) (e i))
    (hL : ∀ v, L (f v) = action e (L v)) :
    ∃ b : Basis (Σ i : Fin n, Fin (e i)) K V,
      LinearMap.toMatrix b b f = shiftMatrix e := by
  classical
  refine ⟨(sumBasis e).map L.symm, ?_⟩
  have ht := toMatrix_of_intertwiner (K := K) (V := V)
    (W := ⨁ i : Fin n, Block (K := K) (e i)) (ι := Σ i : Fin n, Fin (e i))
    (sumBasis (K := K) e) f (action (K := K) e) L hL
  exact ht.trans (toMatrix_action (K := K) e)

theorem exists_shift_basis {n : ℕ} (b₀ : Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ, (∑ i, e i) = n ∧
      ∃ b : Basis (Σ i : Fin n, Fin (e i)) K V,
        LinearMap.toMatrix b b f = shiftMatrix e := by
  classical
  obtain ⟨e, ⟨E⟩⟩ := NilpotentOrbits.nilpotent_decomposition b₀ f hf
  let L : V ≃ₗ[K] ⨁ i : Fin n, Block (K := K) (e i) :=
    (Module.AEval'.of f).trans (E.restrictScalars K)
  have hL (v : V) : L (f v) = action e (L v) := by
    change E (Module.AEval'.of f (f v)) = (X : K[X]) • E (Module.AEval'.of f v)
    rw [← Module.AEval'.X_smul_of, E.map_smul]
  obtain ⟨b, hb⟩ := shift_basis_of_equiv e f L hL
  refine ⟨e, ?_, b, hb⟩
  have hc := (Module.finrank_eq_card_basis b).symm.trans
    (Module.finrank_eq_card_basis b₀)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hc

end PermanentBorder.NilpotentBlocks

namespace PermanentBorder.NilpotentBlocks
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_shape_basis {n : ℕ} (b₀ : Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ, ∃ he : (∑ i, e i) = n,
      ∃ b : Basis (Fin n) K V, LinearMap.toMatrix b b f = shapeMatrix e he := by
  classical
  obtain ⟨e, he, b, hb⟩ := exists_shift_basis b₀ f hf
  refine ⟨e, he, b.reindex (indexEquiv e he), ?_⟩
  ext i j
  simpa only [LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply,
    shapeMatrix, Matrix.reindex_apply, Matrix.submatrix_apply] using
      congrArg (fun M => M ((indexEquiv e he).symm i) ((indexEquiv e he).symm j)) hb

theorem matrix_conjugacy_of_basis {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (b : Basis (Fin n) K (Fin n → K)) :
    ∃ U : (Matrix (Fin n) (Fin n) K)ˣ,
      LinearMap.toMatrix b b (Matrix.toLinAlgEquiv' A) =
        (U : Matrix (Fin n) (Fin n) K) * A * (↑U⁻¹ : Matrix (Fin n) (Fin n) K) := by
  classical
  let E : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) := Matrix.toLinAlgEquiv'
  let B := LinearMap.toMatrix b b (E A)
  have hL (v : Fin n → K) : b.equivFun (E A v) = E B (b.equivFun v) := by
    change b.repr (E A v) = B.mulVec (b.repr v)
    exact (LinearMap.toMatrix_mulVec_repr b b (E A) v).symm
  obtain ⟨U, hU⟩ := NilpotentOrbits.unit_conjugacy_of_intertwiner (E A) (E B) b.equivFun hL
  let W := Units.map E.symm.toRingHom.toMonoidHom U
  refine ⟨W, ?_⟩
  change B = E.symm (U : Module.End K (Fin n → K)) * A *
    E.symm (↑U⁻¹ : Module.End K (Fin n → K))
  have h := congrArg E.symm hU
  simpa only [map_mul, E.symm_apply_apply] using h

theorem canonical_nilpotent_form (K : Type*) [Field K] {L : Type*} [Field L]
    (φ : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (hA : IsNilpotent A) :
    ∃ e : Fin n → ℕ, ∃ he : (∑ i, e i) = n,
      ∃ U : (Matrix (Fin n) (Fin n) L)ˣ,
        (shapeMatrix (K := K) e he).map φ =
          (U : Matrix (Fin n) (Fin n) L) * A * (↑U⁻¹ : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨e, he, b, hb⟩ := exists_shape_basis (Pi.basisFun L (Fin n))
    (Matrix.toLinAlgEquiv' A) (hA.map Matrix.toLinAlgEquiv')
  obtain ⟨U, hU⟩ := matrix_conjugacy_of_basis A b
  exact ⟨e, he, U, by rw [shapeMatrix_map, ← hb]; exact hU⟩

end PermanentBorder.NilpotentBlocks

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PunctualCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CommutingPairs
open Matrix CentralizerDimension CentralizerParameters OrbitNormalization
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem nilpotent_pair_field_bound {n : ℕ} (hn : 0 < n)
    (A B : Matrix (Fin n) (Fin n) L) (hA : IsNilpotent A) (hB : IsNilpotent B)
    (hAB : A * B = B * A) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (n * n - 1 : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hBd : B.det = 0 := by
    obtain ⟨r, hr⟩ := hB
    have hd : B.det ^ r = 0 := by rw [← Matrix.det_pow, hr, Matrix.det_zero]
    by_contra h
    exact pow_ne_zero r h hd
  obtain ⟨e, he, U, hU⟩ := NilpotentBlocks.canonical_nilpotent_form K (algebraMap K L) A hA
  have hP : A * (↑U⁻¹ : Matrix (Fin n) (Fin n) L) =
      (↑U⁻¹ : Matrix (Fin n) (Fin n) L) *
        (NilpotentBlocks.shapeMatrix (K := K) e he).map (algebraMap K L) := by
    rw [hU, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨F, hF, hAF, hBF⟩ := normalized_pair_field_bound A B
    (NilpotentBlocks.shapeMatrix e he) U⁻¹ hP hAB hBd
  refine ⟨F, ?_, hAF, hBF⟩
  have hpos : 0 < n * n := Nat.mul_pos hn hn
  have hc : n * n = (n * n - 1) + 1 := by omega
  rw [hc, Nat.cast_add, Nat.cast_one] at hF
  exact Cardinal.lt_natCast_add_one_iff.mp hF

end PermanentBorder.CommutingPairs

namespace PermanentBorder.FieldParameters
open Algebra MvPolynomial
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem adjoin_trdeg_le {n : ℕ} (x : Fin n → L) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range x)) ≤ (n : Cardinal) := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  have h := trdeg_le_of_surjective (MvPolynomial.aeval (R := K) x).rangeRestrict
    (AlgHom.rangeRestrict_surjective (MvPolynomial.aeval (R := K) x))
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast] using h

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_le {n : ℕ} (x : Fin n → L) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤ (n : Cardinal) := by
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact adjoin_trdeg_le x

theorem extend_field {p n : ℕ} (F : IntermediateField K L)
    (hF : Algebra.trdeg K F ≤ (p : Cardinal)) (x : Fin n → L) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (p + n : ℕ) ∧ (∀ i, x i ∈ E) := by
  let T := IntermediateField.adjoin F (Set.range x)
  let E := T.restrictScalars K
  have : FaithfulSMul F T := (faithfulSMul_iff_algebraMap_injective F T).mpr
    (algebraMap F T).injective
  have : FaithfulSMul K F := (faithfulSMul_iff_algebraMap_injective K F).mpr
    (algebraMap K F).injective
  have hFE : F ≤ E := by
    intro y hy
    exact T.algebraMap_mem ⟨y, hy⟩
  have hx : ∀ i, x i ∈ E := fun i => IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
  refine ⟨E, hFE, ?_, hx⟩
  calc
    Algebra.trdeg K E = Algebra.trdeg K F + Algebra.trdeg F T := (trdeg_add_eq K F (A := T)).symm
    _ ≤ (p : Cardinal) + n := add_le_add hF (field_adjoin_trdeg_le (K := F) x)
    _ = (p + n : ℕ) := by simp only [Nat.cast_add]

end PermanentBorder.FieldParameters

namespace PermanentBorder.GenericMatrix
open Matrix MvPolynomial
universe u
variable (L : Type u) [Field L] (n : ℕ)

theorem relative_trdeg : Algebra.trdeg L (FunctionField L n) = (n * n : ℕ) := by
  have : Algebra.IsAlgebraic (CoordinateRing L n) (FunctionField L n) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (CoordinateRing L n))
  have : FaithfulSMul (CoordinateRing L n) (FunctionField L n) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (CoordinateRing L n) (FunctionField L n))
  rw [← trdeg_add_eq L (CoordinateRing L n), trdeg_eq_zero (R := CoordinateRing L n), add_zero]
  simp only [CoordinateRing, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_prod,
    Cardinal.mk_fin, Cardinal.lift_mul, Cardinal.lift_natCast, Nat.cast_mul]

theorem field_eq_top_of_mem (K : Type u) [Field K] [Algebra K L]
    (E : IntermediateField K (FunctionField L n))
    (hc : ∀ x : L, algebraMap L (FunctionField L n) x ∈ E)
    (hx : ∀ i j, genericMatrix L n i j ∈ E) : E = ⊤ := by
  have hp : ∀ p : CoordinateRing L n,
      algebraMap (CoordinateRing L n) (FunctionField L n) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C x =>
      change algebraMap (CoordinateRing L n) (FunctionField L n)
        (algebraMap L (CoordinateRing L n) x) ∈ E
      rw [← IsScalarTower.algebraMap_apply]
      exact hc x
    | add p q hp hq =>
      rw [map_add]
      exact E.add_mem hp hq
    | mul_X p ij hp =>
      rw [map_mul]
      exact E.mul_mem hp (hx ij.1 ij.2)
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨p, q, _, hz⟩ := IsFractionRing.div_surjective (CoordinateRing L n) z
  rw [← hz]
  exact E.div_mem (hp p) (hp q)

end PermanentBorder.GenericMatrix

namespace PermanentBorder.CyclicFrames
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

theorem recover_frame (r s : ι → ℕ) (A B A' B' Q : Matrix ι ι L)
    (v v' : ι → L) (hb : MonomialBasis r s A B v)
    (hA : A' * Q = Q * A) (hB : B' * Q = Q * B) (hv : v' = Q.mulVec v) :
    ∀ i j, Q i j = ((A' ^ r j * B' ^ s j).mulVec v') i := by
  intro i j
  have hpa : Q * A ^ r j = A' ^ r j * Q := (SemiconjBy.pow_right hA.symm _)
  have hpb : Q * B ^ s j = B' ^ s j * Q := (SemiconjBy.pow_right hB.symm _)
  have hm : (A' ^ r j * B' ^ s j) * Q = Q * (A ^ r j * B ^ s j) := by
    rw [mul_assoc, ← hpb, ← mul_assoc, ← hpa, mul_assoc]
  rw [hv, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hb j,
    Matrix.mulVec_single]
  simp

theorem pow_mem (F : IntermediateField K L) (A : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (r : ℕ) : ∀ i j, (A ^ r) i j ∈ F := by
  induction r with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split <;> simp
  | succ r hr =>
    rw [pow_succ]
    exact MatrixSubfield.mul_mem F _ _ hr hA

omit [DecidableEq ι] in
theorem mulVec_mem (F : IntermediateField K L) (A : Matrix ι ι L) (v : ι → L)
    (hA : ∀ i j, A i j ∈ F) (hv : ∀ i, v i ∈ F) : ∀ i, A.mulVec v i ∈ F := by
  intro i
  exact F.sum_mem fun j _ => F.mul_mem (hA i j) (hv j)

theorem frame_mem (F : IntermediateField K L) (r s : ι → ℕ)
    (A B A' B' Q : Matrix ι ι L) (v v' : ι → L)
    (hb : MonomialBasis r s A B v)
    (hA : A' * Q = Q * A) (hB : B' * Q = Q * B) (hv : v' = Q.mulVec v)
    (hAF : ∀ i j, A' i j ∈ F) (hBF : ∀ i j, B' i j ∈ F) (hvF : ∀ i, v' i ∈ F) :
    ∀ i j, Q i j ∈ F := by
  intro i j
  rw [recover_frame r s A B A' B' Q v v' hb hA hB hv i j]
  exact mulVec_mem F _ _ (MatrixSubfield.mul_mem F _ _
    (pow_mem F A' hAF (r j)) (pow_mem F B' hBF (s j))) hvF i

theorem original_mem (F : IntermediateField K L)
    (A B A' B' : Matrix ι ι L) (Q : (Matrix ι ι L)ˣ) (v v' : ι → L)
    (hA : A' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A)
    (hB : B' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * B)
    (hv : v' = (Q : Matrix ι ι L).mulVec v)
    (hQF : ∀ i j, (Q : Matrix ι ι L) i j ∈ F)
    (hAF : ∀ i j, A' i j ∈ F) (hBF : ∀ i j, B' i j ∈ F) (hvF : ∀ i, v' i ∈ F) :
    (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) ∧ (∀ i, v i ∈ F) := by
  have hQiF := MatrixSubfield.unit_inv_mem F Q hQF
  have he (M M' : Matrix ι ι L) (hM : M' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * M) :
      M = (↑Q⁻¹ : Matrix ι ι L) * (M' * (Q : Matrix ι ι L)) := by
    rw [hM, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [he A A' hA]
    exact MatrixSubfield.mul_mem F _ _ hQiF (MatrixSubfield.mul_mem F _ _ hAF hQF)
  · rw [he B B' hB]
    exact MatrixSubfield.mul_mem F _ _ hQiF (MatrixSubfield.mul_mem F _ _ hBF hQF)
  · have hev : v = (↑Q⁻¹ : Matrix ι ι L).mulVec v' := by
      rw [hv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hev]
    exact mulVec_mem F _ _ hQiF hvF

end PermanentBorder.CyclicFrames

namespace PermanentBorder.CyclicFrames
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Fintype ι] [DecidableEq ι]

theorem conjugation_intertwines (Q : (Matrix ι ι L)ˣ) (A : Matrix ι ι L) :
    conjugation Q A * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A := by
  change ((Q : Matrix ι ι L) * A * (↑Q⁻¹ : Matrix ι ι L)) *
    (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A
  rw [mul_assoc, Units.inv_mul, mul_one]

end PermanentBorder.CyclicFrames
namespace PermanentBorder.PunctualCharts
open Matrix Algebra CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem generated_chart_field_bound {n : ℕ} (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v)
    (hgen : IntermediateField.adjoin K (tripleEntries A B v) = ⊤) :
    Algebra.trdeg K L ≤ (n - 1 : ℕ) := by
  classical
  let T := GenericMatrix.FunctionField L n
  let f := algebraMap L T
  let Q := GenericMatrix.genericUnit L n
  let A₀ : Matrix (Fin n) (Fin n) T := A.map f
  let B₀ : Matrix (Fin n) (Fin n) T := B.map f
  let v₀ : Fin n → T := f ∘ v
  let A' := conjugation Q A₀
  let B' := conjugation Q B₀
  let v' := (Q : Matrix (Fin n) (Fin n) T).mulVec v₀
  have hA' : IsNilpotent A' := (hA.map f.mapMatrix).map (conjugation Q)
  have hB' : IsNilpotent B' := (hB.map f.mapMatrix).map (conjugation Q)
  have hAB' : A' * B' = B' * A' := by
    exact ((Commute.map (show Commute A B from hAB) f.mapMatrix).map (conjugation Q)).eq
  obtain ⟨F, hF, hAF, hBF⟩ := CommutingPairs.nilpotent_pair_field_bound (K := K) hn A' B'
    hA' hB' hAB'
  obtain ⟨E, hFE, hE, hvE⟩ := FieldParameters.extend_field F hF v'
  have hAE : ∀ i j, A' i j ∈ E := fun i j => hFE (hAF i j)
  have hBE : ∀ i j, B' i j ∈ E := fun i j => hFE (hBF i j)
  have hb₀ : MonomialBasis r s A₀ B₀ v₀ := hb.map f
  have hAQ := conjugation_intertwines Q A₀
  have hBQ := conjugation_intertwines Q B₀
  have hQE : ∀ i j, (Q : Matrix (Fin n) (Fin n) T) i j ∈ E :=
    frame_mem E r s A₀ B₀ A' B' Q v₀ v' hb₀ hAQ hBQ rfl hAE hBE hvE
  obtain ⟨hA₀E, hB₀E, hv₀E⟩ := original_mem E A₀ B₀ A' B' Q v₀ v' hAQ hBQ
    rfl hQE hAE hBE hvE
  have hc : ∀ x : L, algebraMap L T x ∈ E := by
    have hle : IntermediateField.adjoin K (tripleEntries A B v) ≤
        IntermediateField.comap (IsScalarTower.toAlgHom K L T) E := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro x ((⟨⟨i,j⟩, rfl⟩ | ⟨⟨i,j⟩, rfl⟩) | ⟨i, rfl⟩)
      · exact hA₀E i j
      · exact hB₀E i j
      · exact hv₀E i
    rw [hgen] at hle
    exact fun x => hle (IntermediateField.mem_top)
  have htop : E = ⊤ := GenericMatrix.field_eq_top_of_mem L n K E hc (by
    simpa only [Q, GenericMatrix.genericUnit_val] using hQE)
  have hT : Algebra.trdeg K T ≤ (n * n - 1 + n : ℕ) := by
    rw [htop, (IntermediateField.topEquiv (F := K) (E := T)).trdeg_eq] at hE
    exact hE
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr
    (algebraMap K L).injective
  have : FaithfulSMul L T := (faithfulSMul_iff_algebraMap_injective L T).mpr
    (algebraMap L T).injective
  rw [← trdeg_add_eq K L, GenericMatrix.relative_trdeg] at hT
  have heq : n * n - 1 + n = (n - 1) + n * n := by
    have hp : 0 < n * n := Nat.mul_pos hn hn
    omega
  rw [heq, Nat.cast_add] at hT
  exact (Cardinal.add_le_add_iff_of_lt_aleph0 (Cardinal.natCast_lt_aleph0)).mp hT

end PermanentBorder.PunctualCharts

namespace PermanentBorder.PunctualCharts
open Matrix Algebra CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem chart_field_bound {n : ℕ} (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (n - 1 : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) ∧ (∀ i, v i ∈ F) := by
  classical
  let F := IntermediateField.adjoin K (tripleEntries A B v)
  have hAF : ∀ i j, A i j ∈ F := fun i j => IntermediateField.subset_adjoin K _
    (Or.inl (Or.inl (Set.mem_range_self (i,j))))
  have hBF : ∀ i j, B i j ∈ F := fun i j => IntermediateField.subset_adjoin K _
    (Or.inl (Or.inr (Set.mem_range_self (i,j))))
  have hvF : ∀ i, v i ∈ F := fun i => IntermediateField.subset_adjoin K _
    (Or.inr (Set.mem_range_self i))
  let A₀ : Matrix (Fin n) (Fin n) F := fun i j => ⟨A i j, hAF i j⟩
  let B₀ : Matrix (Fin n) (Fin n) F := fun i j => ⟨B i j, hBF i j⟩
  let v₀ : Fin n → F := fun i => ⟨v i, hvF i⟩
  let f := (algebraMap F L).mapMatrix (m := Fin n)
  have hf : Function.Injective f := by
    intro P Q h
    ext i j
    exact congrFun (congrFun h i) j
  have hfA : f A₀ = A := rfl
  have hfB : f B₀ = B := rfl
  have hA₀ : IsNilpotent A₀ := by
    obtain ⟨d, hd⟩ := hA
    refine ⟨d, hf ?_⟩
    rw [map_pow, hfA, map_zero, hd]
  have hB₀ : IsNilpotent B₀ := by
    obtain ⟨d, hd⟩ := hB
    refine ⟨d, hf ?_⟩
    rw [map_pow, hfB, map_zero, hd]
  have hAB₀ : A₀ * B₀ = B₀ * A₀ := by
    apply hf
    rw [map_mul, map_mul, hfA, hfB, hAB]
  have hb₀ : MonomialBasis r s A₀ B₀ v₀ := by
    intro i
    ext j
    have he := congrFun (hb i) j
    have hh := (algebraMap F L).map_mulVec (A₀ ^ r i * B₀ ^ s i) v₀ j
    have hp : (A₀ ^ r i * B₀ ^ s i).map (algebraMap F L) = A ^ r i * B ^ s i := by
      change f (A₀ ^ r i * B₀ ^ s i) = _
      rw [map_mul, map_pow, map_pow, hfA, hfB]
    rw [hp] at hh
    change algebraMap F L ((A₀ ^ r i * B₀ ^ s i).mulVec v₀ j) = _
    rw [hh]
    change ((A ^ r i * B ^ s i).mulVec v) j = _
    rw [he]
    by_cases hij : j = i
    · subst j
      simp
    · simp [hij]
  have hgen : IntermediateField.adjoin K (tripleEntries A₀ B₀ v₀) = ⊤ := by
    apply IntermediateField.map_injective F.val
    rw [IntermediateField.adjoin_map]
    have him : F.val '' tripleEntries A₀ B₀ v₀ = tripleEntries A B v := by
      simp only [tripleEntries, Set.image_union, ← Set.range_comp]
      rfl
    rw [him]
    change F = (⊤ : IntermediateField K F).map F.val
    ext x
    constructor
    · intro hx
      exact ⟨⟨x,hx⟩, IntermediateField.mem_top, rfl⟩
    · rintro ⟨x, _, rfl⟩
      exact x.property
  exact ⟨F, generated_chart_field_bound hn r s A₀ B₀ v₀ hA₀ hB₀ hAB₀ hb₀ hgen,
    hAF, hBF, hvF⟩

end PermanentBorder.PunctualCharts

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.CurveParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.CurveParameters
open Matrix Algebra MvPolynomial CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

omit [Infinite K] in

theorem support_field_bound (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (x : Fin 2 → L) (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤ (1 : Cardinal) := by
  have h := ParameterBounds.field_adjoin_trdeg_lt_of_relation x p hp hx
  apply Cardinal.lt_natCast_add_one_iff.mp
  convert h using 1
  norm_num

theorem extend_by_chart {p₀ n : ℕ} (F : IntermediateField K L)
    (hF : Algebra.trdeg K F ≤ (p₀ : Cardinal))
    (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (x : Fin 2 → L) (hx : aeval x p = 0) (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (p₀+n : ℕ) ∧
      (∀ i, x i ∈ E) ∧ (∀ i j, A i j ∈ E) ∧
      (∀ i j, B i j ∈ E) ∧ (∀ i, v i ∈ E) := by
  have : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  let pF := MvPolynomial.map (algebraMap K F) p
  have hpF : pF ≠ 0 := by
    exact fun h => hp ((MvPolynomial.map_injective _ (algebraMap K F).injective)
      (by simpa only [map_zero] using h))
  have hxF : aeval (R := F) x pF = 0 := by
    change eval₂ (algebraMap F L) x (MvPolynomial.map (algebraMap K F) p) = 0
    rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq K F L]
    exact hx
  let T := IntermediateField.adjoin F (Set.range x)
  have : IsScalarTower K T L := IsScalarTower.of_algebraMap_eq' (by ext z; rfl)
  have : Infinite T := Infinite.of_injective (algebraMap K T) (algebraMap K T).injective
  have hT : Algebra.trdeg F T ≤ (1 : Cardinal) := support_field_bound pF hpF x hxF
  obtain ⟨U,hU,hAU,hBU,hvU⟩ := PunctualCharts.chart_field_bound (K := T)
    hn r s A B v hA hB hAB hb
  have : FaithfulSMul T U := (faithfulSMul_iff_algebraMap_injective T U).mpr
    (algebraMap T U).injective
  let E := U.restrictScalars K
  have : FaithfulSMul K F := (faithfulSMul_iff_algebraMap_injective K F).mpr
    (algebraMap K F).injective
  have : FaithfulSMul F T := (faithfulSMul_iff_algebraMap_injective F T).mpr
    (algebraMap F T).injective
  have : FaithfulSMul K T := (faithfulSMul_iff_algebraMap_injective K T).mpr
    (algebraMap K T).injective
  have hFE : F ≤ E := by
    intro z hz
    exact U.algebraMap_mem (algebraMap F T ⟨z,hz⟩)
  have hxE : ∀ i, x i ∈ E := fun i =>
    U.algebraMap_mem ⟨x i, IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
  refine ⟨E,hFE,?_,hxE,hAU,hBU,hvU⟩
  calc
    Algebra.trdeg K E = Algebra.trdeg K T + Algebra.trdeg T U :=
      (trdeg_add_eq K T (A := U)).symm
    _ = (Algebra.trdeg K F + Algebra.trdeg F T) + Algebra.trdeg T U := by
      rw [trdeg_add_eq K F (A := T)]
    _ ≤ ((p₀ : Cardinal) + 1) + (n-1 : ℕ) := add_le_add (add_le_add hF hT) hU
    _ = (p₀+n : ℕ) := by
      rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hn, ← Nat.cast_add]

end PermanentBorder.CurveParameters
namespace PermanentBorder.CurveParameters
open Matrix Algebra MvPolynomial CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

namespace LocalChart
variable {p : MvPolynomial (Fin 2) K}

theorem InField.mono {D : LocalChart (L := L) p} {F E : IntermediateField K L}
    (h : D.InField F) (hFE : F ≤ E) : D.InField E :=
  ⟨fun i => hFE (h.1 i),fun i j => hFE (h.2.1 i j),
    fun i j => hFE (h.2.2.1 i j),fun i => hFE (h.2.2.2 i)⟩

theorem extend [Infinite K] (D : LocalChart (L := L) p) (hp : p ≠ 0)
    {b : ℕ} (F : IntermediateField K L) (hF : Algebra.trdeg K F ≤ (b : Cardinal)) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (b + D.length : ℕ) ∧ D.InField E :=
  extend_by_chart F hF p hp D.support D.on_curve D.positive D.r D.s D.A D.B D.v
    D.nilA D.nilB D.commutes D.basis_eq

end LocalChart

theorem extend_by_finite_family [Infinite K] {κ : Type*}
    {p : MvPolynomial (Fin 2) K} (hp : p ≠ 0)
    (D : κ → LocalChart (L := L) p) (t : Finset κ)
    {b : ℕ} (F : IntermediateField K L) (hF : Algebra.trdeg K F ≤ (b : Cardinal)) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (b + ∑ i ∈ t, (D i).length : ℕ) ∧
      ∀ i ∈ t, (D i).InField E := by
  classical
  induction t using Finset.induction_on generalizing b F with
  | empty =>
    exact ⟨F,le_rfl,by simpa using hF,by simp⟩
  | @insert i t hi ih =>
    obtain ⟨T,hFT,hT,hDT⟩ := (D i).extend hp F hF
    obtain ⟨E,hTE,hE,hDE⟩ := ih T hT
    refine ⟨E,hFT.trans hTE,?_,?_⟩
    · simpa only [Finset.sum_insert hi, Nat.add_assoc] using hE
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjt
      · subst j
        exact hDT.mono hTE
      · exact hDE j hjt

end PermanentBorder.CurveParameters

namespace PermanentBorder.FiniteAlgebras
open Module
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R] [Module.Finite L R]

include L in

theorem artinian : IsArtinianRing R := isArtinian_of_tower L inferInstance

end PermanentBorder.FiniteAlgebras

namespace PermanentBorder.FinitePlaneFrames
open MvPolynomial Module Matrix
variable {L S : Type*} [Field L] [CommRing S] [Algebra L S]

theorem action_on_unit {n : ℕ} (b : Basis (Fin n) L S) (x : S) :
    (representation b x).mulVec (unitVector b) = b.equivFun x := by
  change ((LinearMap.toMatrix b b) (Algebra.lmul L S x)).mulVec
    (fun i => b.repr 1 i) = _
  rw [LinearMap.toMatrix_mulVec_repr]
  simp only [Module.Basis.equivFun_apply]
  change (fun i => b.repr (x * 1) i) = _
  rw [mul_one]

theorem exists_monomial_basis [Module.Finite L S]
    (q : MvPolynomial (Fin 2) L →ₐ[L] S) (hq : Function.Surjective q) :
    ∃ (b : Basis (Fin (finrank L S)) L S) (r s : Fin (finrank L S) → ℕ),
      ∀ i, b i = q (X 0 ^ r i * X 1 ^ s i) := by
  classical
  let μ := q.toLinearMap ∘ (MvPolynomial.basisMonomials (Fin 2) L)
  have hsp : Submodule.span L (Set.range μ) = ⊤ := by
    rw [show Set.range μ = q.toLinearMap '' Set.range (MvPolynomial.basisMonomials (Fin 2) L) from
      Set.range_comp _ _]
    rw [← Submodule.map_span, (MvPolynomial.basisMonomials (Fin 2) L).span_eq,
      Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hq
  have hdim : finrank L (Submodule.span L (Set.range μ)) = finrank L S := by
    rw [hsp, finrank_top]
  obtain ⟨f,hmem,hspan,hind⟩ : ∃ f : Fin (finrank L S) → S,
      (∀ i, f i ∈ Set.range μ) ∧ Submodule.span L (Set.range f) = ⊤ ∧
        LinearIndependent L f := by
    have he := Submodule.exists_fun_fin_finrank_span_eq L (Set.range μ)
    rw [hdim] at he
    simpa only [hsp] using he
  choose e he using hmem
  let b := Basis.mk hind (le_of_eq hspan.symm)
  refine ⟨b,fun i => e i 0,fun i => e i 1,?_⟩
  intro i
  rw [show b i = f i from Basis.mk_apply hind (le_of_eq hspan.symm) i, ← he i]
  change q (monomial (e i) 1) = _
  congr 1
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_two]
  · simp

end PermanentBorder.FinitePlaneFrames
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial Matrix FinitePlaneFrames
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R]
  [Module.Finite L R] [IsAlgClosed L]

theorem shiftedLocalHom_surjective (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (hq : Function.Surjective q) (m : MaximalSpectrum R) (e : ℕ) :
    Function.Surjective (shiftedLocalHom L R q m e) :=
  Ideal.Quotient.mk_surjective.comp (hq.comp
    (PlaneTranslations.equivalence (-supportPoint L R q m)).surjective)

theorem local_monomial_chart (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (hq : Function.Surjective q) (m : MaximalSpectrum R) (e : ℕ) :
    ∃ (b : Basis (Fin (finrank L (R ⧸ m.asIdeal ^ e))) L (R ⧸ m.asIdeal ^ e))
      (r s : Fin (finrank L (R ⧸ m.asIdeal ^ e)) → ℕ),
      CyclicFrames.MonomialBasis r s
        (representation b (shiftedLocalHom L R q m e (X 0)))
        (representation b (shiftedLocalHom L R q m e (X 1))) (unitVector b) := by
  obtain ⟨b,r,s,hb⟩ := FinitePlaneFrames.exists_monomial_basis
    (shiftedLocalHom L R q m e) (shiftedLocalHom_surjective L R q hq m e)
  refine ⟨b,r,s,?_⟩
  intro i
  have h : (representation b (shiftedLocalHom L R q m e (X 0))) ^ r i *
      (representation b (shiftedLocalHom L R q m e (X 1))) ^ s i =
      representation b (shiftedLocalHom L R q m e (X 0 ^ r i * X 1 ^ s i)) := by
    simp only [map_mul, map_pow]
  rw [h, action_on_unit, ← hb i]
  ext j
  simpa only [Pi.single_apply, eq_comm] using b.equivFun_self i j

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.FiniteAlgebras
open Module
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem exists_canonical_local_power_decomposition :
    ∃ e : ℕ, 0 < e ∧ ∃ E : R ≃ₐ[L] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ e,
      ∀ x m, E x m = Ideal.Quotient.mk (m.asIdeal ^ e) x := by
  have : IsArtinianRing R := artinian L R
  obtain ⟨e,he⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  have he' : nilradical R ^ (e+1) = ⊥ := by rw [pow_succ, he]; simp
  let E := ((AlgEquiv.quotientBot R R).symm.trans
    ((Ideal.quotientEquivAlgOfEq R he'.symm).trans
      (IsArtinianRing.quotNilradicalPowEquivPi R (e+1)))).restrictScalars L
  exact ⟨e+1, Nat.zero_lt_succ e, E, fun _ _ => rfl⟩

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.BasisFieldRecovery
open Module Matrix
variable {K L S ι κ : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup S] [Module L S] [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem repr_mem (F : IntermediateField K L) (b : Basis ι L S) (c : Basis κ L S)
    (hbc : ∀ i j, c.repr (b j) i ∈ F) (x : S) (hx : ∀ i, c.repr x i ∈ F) :
    ∀ j, b.repr x j ∈ F := by
  classical
  let e := b.indexEquiv c
  let b' := b.reindex e
  let P : (Matrix κ κ L)ˣ :=
    ⟨c.toMatrix b', b'.toMatrix c,
      c.toMatrix_mul_toMatrix_flip b', b'.toMatrix_mul_toMatrix_flip c⟩
  have hP : ∀ i j, (P : Matrix κ κ L) i j ∈ F := by
    intro i j
    simpa only [P, Units.val_mk, b', Basis.toMatrix_apply, Basis.reindex_apply] using hbc i (e.symm j)
  have hI := MatrixSubfield.unit_inv_mem F P hP
  have hb'x : ∀ j, b'.repr x j ∈ F := by
    intro j
    rw [← c.toMatrix_mulVec_repr b' x]
    exact F.sum_mem fun i _ => F.mul_mem (hI j i) (hx i)
  intro j
  have h := hb'x (e j)
  simpa only [b', Basis.repr_reindex, Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply, Finsupp.mapDomain_apply e.injective] using h

end PermanentBorder.BasisFieldRecovery

namespace PermanentBorder.MatrixSubfield
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

theorem pow_mem (F : IntermediateField K L) (A : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (r : ℕ) : ∀ i j, (A ^ r) i j ∈ F := by
  induction r with
  | zero => intro i j; simp only [pow_zero, one_apply]; split <;> simp
  | succ r ih => simpa only [pow_succ] using mul_mem F (A^r) A ih hA

omit [DecidableEq ι] in
theorem mulVec_mem (F : IntermediateField K L) (A : Matrix ι ι L) (v : ι → L)
    (hA : ∀ i j, A i j ∈ F) (hv : ∀ i, v i ∈ F) :
    ∀ i, (A.mulVec v) i ∈ F := by
  intro i
  exact F.sum_mem fun j _ => F.mul_mem (hA i j) (hv j)

end PermanentBorder.MatrixSubfield

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.QuotientFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.FinitePlaneFrames
open Module Matrix MvPolynomial
variable {K L S : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing S] [Algebra L S]

theorem monomial_coordinates_mem {n : ℕ} (F : IntermediateField K L)
    (q : MvPolynomial (Fin 2) L →ₐ[L] S) (b : Basis (Fin n) L S)
    (hA : ∀ i j, representation b (q (X 0)) i j ∈ F)
    (hB : ∀ i j, representation b (q (X 1)) i j ∈ F)
    (hv : ∀ i, unitVector b i ∈ F) (r s : ℕ) :
    ∀ i, b.repr (q (X 0 ^ r * X 1 ^ s)) i ∈ F := by
  have h := MatrixSubfield.mulVec_mem F
    ((representation b (q (X 0))) ^ r * (representation b (q (X 1))) ^ s)
    (unitVector b)
    (MatrixSubfield.mul_mem F _ _ (MatrixSubfield.pow_mem F _ hA r)
      (MatrixSubfield.pow_mem F _ hB s)) hv
  have he : (representation b (q (X 0))) ^ r * (representation b (q (X 1))) ^ s =
      representation b (q (X 0 ^ r * X 1 ^ s)) := by simp only [map_mul,map_pow]
  simpa only [he, action_on_unit, Basis.equivFun_apply] using h

theorem unshifted_representation_mem {n : ℕ} (F : IntermediateField K L)
    (b : Basis (Fin n) L S) (x : S) (a : L) (ha : a ∈ F)
    (h : ∀ i j, representation b (x - algebraMap L S a) i j ∈ F) :
    ∀ i j, representation b x i j ∈ F := by
  have he : representation b x = representation b (x - algebraMap L S a) +
      algebraMap L (Matrix (Fin n) (Fin n) L) a := by
    rw [map_sub, AlgHom.commutes, sub_add_cancel]
  intro i j
  rw [he, Matrix.add_apply]
  refine F.add_mem (h i j) ?_
  change (Matrix.scalar (Fin n) a) i j ∈ F
  by_cases hij : i = j
  · subst j; simpa using ha
  · simp [Matrix.scalar, Matrix.diagonal, hij]

end PermanentBorder.FinitePlaneFrames
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial Matrix FinitePlaneFrames CurveParameters
universe u
variable {K L : Type u} {R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R] [Module.Finite L R] [IsAlgClosed L]

theorem local_monomial_coordinates_mem (F : IntermediateField K L)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (p : MvPolynomial (Fin 2) K) (hpq : q (p.map (algebraMap K L)) = 0)
    (m : MaximalSpectrum R) (e : ℕ) (he : 0 < e)
    (b : Basis (Fin (finrank L (R ⧸ m.asIdeal ^ e))) L (R ⧸ m.asIdeal ^ e))
    (r s : Fin (finrank L (R ⧸ m.asIdeal ^ e)) → ℕ)
    (hb : CyclicFrames.MonomialBasis r s
      (representation b (shiftedLocalHom L R q m e (X 0)))
      (representation b (shiftedLocalHom L R q m e (X 1))) (unitVector b))
    (hF : (localChart q p hpq m e he b r s hb).InField F) (r' s' : ℕ) :
    ∀ i, b.repr (localHom L R q m e (X 0 ^ r' * X 1 ^ s')) i ∈ F := by
  apply monomial_coordinates_mem F (localHom L R q m e) b _ _ hF.2.2.2 r' s'
  · apply unshifted_representation_mem F b _ (supportPoint L R q m 0) (hF.1 0)
    have h : ∀ i j, representation b (shiftedLocalHom L R q m e (X 0)) i j ∈ F := hF.2.1
    simpa only [shiftedLocalHom_X] using h
  · apply unshifted_representation_mem F b _ (supportPoint L R q m 1) (hF.1 1)
    have h : ∀ i j, representation b (shiftedLocalHom L R q m e (X 1)) i j ∈ F := hF.2.2.1
    simpa only [shiftedLocalHom_X] using h

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.CurveQuotientParameters
open Module Matrix MvPolynomial FiniteAlgebras FinitePlaneFrames CurveParameters
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [Infinite K] [IsAlgClosed L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem chart_field_bound (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (hq : Function.Surjective q)
    (hpq : q (p.map (algebraMap K L)) = 0)
    {n : ℕ} (b₀ : Basis (Fin n) L R) (r₀ s₀ : Fin n → ℕ)
    (hb₀ : ∀ i, b₀ i = q (X 0 ^ r₀ i * X 1 ^ s₀ i)) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (finrank L R : Cardinal) ∧
      (∀ i j, representation b₀ (q (X 0)) i j ∈ F) ∧
      (∀ i j, representation b₀ (q (X 1)) i j ∈ F) ∧
      (∀ i, unitVector b₀ i ∈ F) := by
  classical
  have : IsArtinianRing R := artinian L R
  let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  obtain ⟨e, he, E, hE⟩ := exists_canonical_local_power_decomposition L R
  choose b r s hb using fun m => local_monomial_chart L R q hq m e
  let D : MaximalSpectrum R → LocalChart (L := L) p := fun m =>
    localChart q p hpq m e he (b m) (r m) (s m) (hb m)
  have hbot : Algebra.trdeg K (⊥ : IntermediateField K L) ≤ (0 : Cardinal) := by
    rw [trdeg_eq_zero]
  obtain ⟨F, _, hF, hDF⟩ := extend_by_finite_family hp D Finset.univ
    (⊥ : IntermediateField K L) hbot
  have hdF : ∀ m, (D m).InField F := fun m => hDF m (Finset.mem_univ m)
  have hlen : finrank L R = ∑ m : MaximalSpectrum R, finrank L (R ⧸ m.asIdeal ^ e) := by
    rw [E.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  have hdeg : Algebra.trdeg K F ≤ (finrank L R : Cardinal) := by
    rw [hlen]
    simpa only [D, localChart, Nat.zero_add] using hF
  let w : R ≃ₗ[L] ((m : MaximalSpectrum R) × Fin (finrank L (R ⧸ m.asIdeal ^ e))) → L :=
    E.toLinearEquiv.trans ((LinearEquiv.piCongrRight fun m => (b m).equivFun).trans
      (LinearEquiv.piCurry L (fun (m : MaximalSpectrum R) (_ : Fin (finrank L (R ⧸ m.asIdeal ^ e))) => L)).symm)
  let c := Basis.ofEquivFun w
  have hmon (a d : ℕ) : ∀ i, c.repr (q (X 0 ^ a * X 1 ^ d)) i ∈ F := by
    intro i
    change (b i.1).repr (E (q (X 0 ^ a * X 1 ^ d)) i.1) i.2 ∈ F
    rw [hE]
    exact local_monomial_coordinates_mem F q p hpq i.1 e he
      (b i.1) (r i.1) (s i.1) (hb i.1) (hdF i.1) a d i.2
  have hbc : ∀ i j, c.repr (b₀ j) i ∈ F := by
    intro i j
    rw [hb₀]
    exact hmon (r₀ j) (s₀ j) i
  have hmon₀ (a d : ℕ) : ∀ i, b₀.repr (q (X 0 ^ a * X 1 ^ d)) i ∈ F :=
    BasisFieldRecovery.repr_mem F b₀ c hbc _ (hmon a d)
  refine ⟨F,hdeg,?_,?_,?_⟩
  · intro i j
    rw [show representation b₀ (q (X 0)) i j = b₀.repr (q (X 0) * b₀ j) i from
      LinearMap.toMatrixAlgEquiv_apply b₀ (Algebra.lmul L R (q (X 0))) i j]
    have h : q (X 0) * b₀ j = q (X 0 ^ (r₀ j + 1) * X 1 ^ s₀ j) := by
      rw [hb₀, ← map_mul]
      congr 1
      ring
    rw [h]
    exact hmon₀ (r₀ j+1) (s₀ j) i
  · intro i j
    rw [show representation b₀ (q (X 1)) i j = b₀.repr (q (X 1) * b₀ j) i from
      LinearMap.toMatrixAlgEquiv_apply b₀ (Algebra.lmul L R (q (X 1))) i j]
    have h : q (X 1) * b₀ j = q (X 0 ^ r₀ j * X 1 ^ (s₀ j+1)) := by
      rw [hb₀, ← map_mul]
      congr 1
      ring
    rw [h]
    exact hmon₀ (r₀ j) (s₀ j+1) i
  · intro i
    simpa only [pow_zero, one_mul, map_one, unitVector, Basis.equivFun_apply] using hmon₀ 0 0 i

end PermanentBorder.CurveQuotientParameters

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Module
variable {K : Type*} [Field K] {k : ℕ}

theorem rowBasis_repr (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    (P : K[X][X]) (hP : TotalDegreeLE P (k-1)) (i : PlaneIndex (k-1)) :
    (rowBasis θ hθ A hk).repr ((Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A))) P) i =
      (P.coeff i.val.1.val).coeff (i.val.2.val-i.val.1.val-1) := by
  let E := rowCoordinates θ hθ A hk
  let q := Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A))
  let v := E.symm (q P)
  have he : q (planeMap (k-1) v) = q P := E.apply_symm_apply (q P)
  have hm : planeMap (k-1) v - P ∈ rowIdeal (pencilBase θ A) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (planeMap (k-1) v - P) = 0
    rw [map_sub, he, sub_self]
  have hz := rowIdeal_low_degree_zero θ hθ A hk hm
    ((totalDegreeLE_planeMap (k-1) v).sub hP)
  have hh := congrArg (fun p : K[X][X] => (p.coeff i.val.1.val).coeff
    (i.val.2.val-i.val.1.val-1)) (sub_eq_zero.mp hz)
  change v i = _
  simpa only [coeff_planeMap] using hh

end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.Bivariate
open Polynomial
variable (K : Type*) [CommSemiring K]

variable {K} {L : Type*} [CommSemiring L]

theorem equivalence_map (f : K →+* L) (p : MvPolynomial (Fin 2) K) :
    equivalence L (MvPolynomial.map f p) = map f (equivalence K p) := by
  have h : (equivalence L).toRingHom.comp (MvPolynomial.map f) =
      (map f).comp (equivalence K).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [map]
    · intro i
      fin_cases i <;> simp [map]
  exact RingHom.congr_fun h p

end PermanentBorder.Bivariate

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

theorem InField.add {F : IntermediateField K L} {P Q : L[X][X]}
    (hP : InField F P) (hQ : InField F Q) : InField F (P+Q) := by
  intro a b
  simp only [coeff_add]
  exact F.add_mem (hP a b) (hQ a b)

theorem InField.sub {F : IntermediateField K L} {P Q : L[X][X]}
    (hP : InField F P) (hQ : InField F Q) : InField F (P-Q) := by
  intro a b
  simp only [coeff_sub]
  exact F.sub_mem (hP a b) (hQ a b)

theorem InField.mul {F : IntermediateField K L} {P Q : L[X][X]}
    (hP : InField F P) (hQ : InField F Q) : InField F (P*Q) := by
  obtain ⟨P',rfl⟩ := (inField_iff_lifts F P).mp hP
  obtain ⟨Q',rfl⟩ := (inField_iff_lifts F Q).mp hQ
  exact (inField_iff_lifts F _).mpr ⟨P'*Q', map_mul _ _ _⟩

theorem inField_map (F : IntermediateField K L) (P : K[X][X]) :
    InField F (map (algebraMap K L) P) := by
  intro a b
  simp only [map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  exact F.algebraMap_mem _

theorem inField_C_C (F : IntermediateField K L) (a : L) (ha : a ∈ F) :
    InField F (C (C a)) := by
  apply (inField_iff_lifts F _).mpr
  exact ⟨C (C ⟨a,ha⟩), by simp [map]⟩

theorem inField_X (F : IntermediateField K L) : InField F (X : L[X][X]) := by
  exact (inField_iff_lifts F _).mpr ⟨X, by simp [map]⟩

theorem inField_C_X (F : IntermediateField K L) : InField F (C (X : L[X])) := by
  exact (inField_iff_lifts F _).mpr ⟨C X, by simp [map]⟩

theorem eval_mem (F : IntermediateField K L) (P : L[X])
    (hP : ∀ a, P.coeff a ∈ F) (t : L) (ht : t ∈ F) : P.eval t ∈ F := by
  rw [Polynomial.eval_eq_sum_range]
  exact F.sum_mem fun a _ => F.mul_mem (hP a) (pow_mem ht a)

end PermanentBorder.Bivariate

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Module
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem coordinates_mem {R ι : Type*} [AddCommGroup R] [Module L R]
    (F : IntermediateField K L) (f : L[X][X] →ₗ[L] R) (b : Basis ι L R)
    (hmon : ∀ a d i, b.repr (f (monomial a (monomial d 1))) i ∈ F)
    (P : L[X][X]) (hP : Bivariate.InField F P) (i : ι) :
    b.repr (f P) i ∈ F := by
  rw [eq_sum_bivariate P, map_sum, map_sum, Finsupp.finsetSum_apply]
  apply F.sum_mem
  intro a _
  rw [map_sum, map_sum, Finsupp.finsetSum_apply]
  apply F.sum_mem
  intro d _
  have he : monomial a (monomial d ((P.coeff a).coeff d)) =
      ((P.coeff a).coeff d) • monomial a (monomial d (1 : L)) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact F.mul_mem (hP a d) (hmon a d i)

variable {k : ℕ}

theorem scaled_coeff_mem (F : IntermediateField K L) (P : L[X][X])
    (hP : Bivariate.InField F P) (a d : ℕ) :
    ((scaleHom P).coeff a).coeff d ∈ F := by
  rw [coeff_scaleHom]
  split_ifs
  · exact hP _ _
  · exact F.zero_mem

omit [Algebra K L] in

theorem map_rowEntry (f : K →+* L) (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i : Fin (k+1)) :
    Bivariate.map f (rowEntry (pencilBase θ A) i) =
      rowEntry (pencilBase (fun j => f (θ j)) (A.map f)) i := by
  have hp : (pencilMatrix (pencilBase θ A)).map (Bivariate.map f) =
      pencilMatrix (pencilBase (fun j => f (θ j)) (A.map f)) := by
    apply Matrix.ext
    intro j l
    by_cases hjl : j=l <;> simp [pencilMatrix, pencilBase, Bivariate.map,
      hjl]
  have ha := (Bivariate.map f).map_adjugate (pencilMatrix (pencilBase θ A))
  change (pencilMatrix (pencilBase θ A)).adjugate.map (Bivariate.map f) =
    ((pencilMatrix (pencilBase θ A)).map (Bivariate.map f)).adjugate at ha
  rw [hp] at ha
  simp only [rowEntry, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (congrFun ha j) i

end PermanentBorder.AdjugateAlgebra

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.DeterminantFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Module
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {k : ℕ}

theorem low_coefficients_mem (F : IntermediateField K L)
    (θ : Fin (k+1) → L) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (hk : 0 < k)
    (P : L[X][X]) (hP : TotalDegreeLE P (k-1))
    (hcoord : ∀ i, (rowBasis θ hθ A hk).repr
      ((Ideal.Quotient.mkₐ L (rowIdeal (pencilBase θ A))) P) i ∈ F) :
    Bivariate.InField F P := by
  intro a b
  by_cases hab : a+b ≤ k-1
  · let i : PlaneIndex (k-1) := ⟨(⟨a,by omega⟩,⟨a+b+1,by omega⟩),by
      change a < a+b+1
      omega⟩
    have h := hcoord i
    rw [rowBasis_repr θ hθ A hk P hP] at h
    change (P.coeff a).coeff (a+b+1-a-1) ∈ F at h
    rwa [show a+b+1-a-1=b by omega] at h
  · rw [hP a b (by omega)]
    exact F.zero_mem

theorem rowEntry_inField (F : IntermediateField K L)
    (θ : Fin (k+1) → L) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (hk : 0 < k)
    (hθF : ∀ i, θ i ∈ F)
    (hmon : ∀ a d i, (rowBasis θ hθ A hk).repr
      ((Ideal.Quotient.mkₐ L (rowIdeal (pencilBase θ A)))
        (monomial a (monomial d 1))) i ∈ F) (j : Fin (k+1)) :
    Bivariate.InField F (rowEntry (pencilBase θ A) j) := by
  let q := Ideal.Quotient.mkₐ L (rowIdeal (pencilBase θ A))
  let P := rowEntry (pencilBase θ A) j
  let P₀ := rowEntry (pencilBase θ 0) j
  have hP₀ : Bivariate.InField F P₀ := by
    apply (Bivariate.inField_iff_lifts F _).mpr
    refine ⟨rowEntry (pencilBase (fun i => (⟨θ i,hθF i⟩ : F)) 0) j,?_⟩
    rw [map_rowEntry]
    rfl
  have hdeg : TotalDegreeLE (P-P₀) (k-1) := by
    apply TotalDegreeLE.pred_of_top_zero hk
    · exact (totalDegreeLE_rowEntry θ A j).sub (totalDegreeLE_rowEntry θ 0 j)
    · simp only [P,P₀,map_sub,coeff_sub,rowEntry_top,sub_self]
  have hzero : q P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
  have hlow : Bivariate.InField F (P-P₀) := by
    apply low_coefficients_mem F θ hθ A hk _ hdeg
    intro i
    change (rowBasis θ hθ A hk).repr (q (P-P₀)) i ∈ F
    rw [map_sub,hzero,zero_sub,map_neg,Finsupp.neg_apply]
    exact F.neg_mem (coordinates_mem F q.toLinearMap (rowBasis θ hθ A hk) hmon P₀ hP₀ i)
  simpa only [sub_add_cancel] using hlow.add hP₀

theorem column_contraction (θ : Fin (k+1) → L)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (j : Fin (k+1)) :
    rowContraction θ A (fun i => A i j) = (pencilMatrix (pencilBase θ A)).det -
      (X + C (X * C (θ j))) * rowEntry (pencilBase θ A) j := by
  classical
  let v : Fin (k+1) → L[X] := Pi.single j 1
  have hv : rowPair (pencilBase θ A) v = rowEntry (pencilBase θ A) j := by
    simp [v,rowPair_eq_sum,Pi.single_apply,apply_ite]
  have hc : (pencilBase θ A).mulVec v =
      (X * C (θ j)) • v + fun i => C (A i j) := by
    funext i
    by_cases hij : i=j
    · subst i
      simp [pencilBase,v,Matrix.mulVec_single]
    · simp [pencilBase,v,Matrix.mulVec_single,hij]
  have hh := X_mul_rowPair (pencilBase θ A) v
  rw [rowPair_neg,hc,rowPair_add,rowPair_smul,hv] at hh
  have hs : (∑ i, v i) = 1 := by simp [v,Pi.single_apply]
  rw [hs,map_one,one_mul] at hh
  change X * rowEntry (pencilBase θ A) j =
    -(C (X*C (θ j)) * rowEntry (pencilBase θ A) j +
      rowContraction θ A (fun i => A i j)) + _ at hh
  linear_combination hh

theorem determinant_mem_rowIdeal (θ : Fin (k+1) → L)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) :
    (pencilMatrix (pencilBase θ A)).det ∈ rowIdeal (pencilBase θ A) := by
  have h := column_contraction θ A 0
  have he : (pencilMatrix (pencilBase θ A)).det =
      rowContraction θ A (fun i => A i 0) +
      (X+C (X*C (θ 0))) * rowEntry (pencilBase θ A) 0 := by
    linear_combination -h
  rw [he]
  exact Ideal.add_mem _ (rowContraction_mem θ A _) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0,rfl⟩))

end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Module
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {k : ℕ}

theorem slopeTrace_eval (θ v : Fin (k+1) → L) (i : Fin (k+1)) :
    (slopeTrace θ v).eval (-θ i) =
      v i * ∏ l ∈ Finset.univ.erase i, (-θ i + θ l) := by
  classical
  simp only [slopeTrace,spectralSlope,Matrix.adjugate_diagonal,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,Matrix.map_apply,Matrix.diagonal_apply_eq,
    eval_finsetSum,eval_mul,eval_C,eval_prod,eval_add,eval_X]
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hp : ∏ l ∈ Finset.univ.erase j, (-θ i + θ l) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hji,Finset.mem_univ i⟩)
      simp
    simp [hp]
  · simp

theorem matrix_inField_of_rows (F : IntermediateField K L)
    (θ : Fin (k+1) → L) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L)
    (hθF : ∀ i, θ i ∈ F)
    (hdet : Bivariate.InField F (pencilMatrix (pencilBase θ A)).det)
    (hrow : ∀ j, Bivariate.InField F (rowEntry (pencilBase θ A) j)) :
    ∀ i j, A i j ∈ F := by
  classical
  intro i j
  have hlin : Bivariate.InField F (X + C (X * C (θ j))) := by
    rw [map_mul]
    exact (Bivariate.inField_X F).add
      ((Bivariate.inField_C_X F).mul (Bivariate.inField_C_C F _ (hθF j)))
  have hc : Bivariate.InField F (rowContraction θ A (fun l => A l j)) := by
    rw [column_contraction]
    exact hdet.sub (hlin.mul (hrow j))
  have hs : ∀ a, (slopeTrace θ (fun l => A l j)).coeff a ∈ F := by
    intro a
    rw [← rowContraction_top θ A]
    exact scaled_coeff_mem F _ hc k a
  have he := Bivariate.eval_mem F _ hs (-θ i) (F.neg_mem (hθF i))
  rw [slopeTrace_eval] at he
  have hp : (∏ l ∈ Finset.univ.erase i, (-θ i + θ l)) ∈ F := by
    exact F.prod_mem fun l _ => F.add_mem (F.neg_mem (hθF i)) (hθF l)
  have hn : (∏ l ∈ Finset.univ.erase i, (-θ i + θ l)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl hz
    have hei : θ l = θ i := by linear_combination hz
    exact (Finset.mem_erase.mp hl).1 (hθ hei)
  simpa only [mul_div_cancel_right₀ _ hn] using F.div_mem he hp

end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.Bivariate
open Module Polynomial
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [Infinite K] [IsAlgClosed L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem quotient_field_bound (p : K[X][X]) (hp : p ≠ 0)
    (q : L[X][X] →ₐ[L] R) (hq : Function.Surjective q)
    (hpq : q (map (algebraMap K L) p) = 0)
    {n : ℕ} (b : Basis (Fin n) L R) (r s : Fin n → ℕ)
    (hb : ∀ i, b i = q (monomial (r i) (monomial (s i) 1))) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (finrank L R : Cardinal) ∧
      ∀ a d i, b.repr (q (monomial a (monomial d 1))) i ∈ F := by
  let q' := q.comp (equivalence L).toAlgHom
  let p' := (equivalence K).symm p
  have hp' : p' ≠ 0 := fun h => hp ((equivalence K).symm.injective (h.trans (map_zero _).symm))
  have hq' : Function.Surjective q' := hq.comp (equivalence L).surjective
  have hpq' : q' (MvPolynomial.map (algebraMap K L) p') = 0 := by
    change q (equivalence L (MvPolynomial.map (algebraMap K L) p')) = 0
    rw [equivalence_map, AlgEquiv.apply_symm_apply]
    exact hpq
  have hb' : ∀ i, b i = q' (MvPolynomial.X 0 ^ r i * MvPolynomial.X 1 ^ s i) := by
    intro i
    change b i = q (equivalence L _)
    rw [equivalence_monomial, hb]
  obtain ⟨F,hF,hA,hB,hv⟩ := CurveQuotientParameters.chart_field_bound p' hp' q' hq' hpq' b r s hb'
  refine ⟨F,hF,?_⟩
  intro a d i
  have h := FinitePlaneFrames.monomial_coordinates_mem F q' b hA hB hv a d i
  simpa only [q', AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, equivalence_monomial] using h

end PermanentBorder.Bivariate

namespace PermanentBorder.DeterminantFibers
open Polynomial Module AdjugateAlgebra
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Infinite K] [IsAlgClosed L] {k : ℕ}

theorem matrix_field_bound (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (hk : 0 < k)
    (p : K[X][X]) (hp : p ≠ 0)
    (hdet : (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det =
      Bivariate.map (algebraMap K L) p) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ ((k+1).choose 2 : Cardinal) ∧ ∀ i j, A i j ∈ F := by
  classical
  let θ' : Fin (k+1) → L := fun i => algebraMap K L (θ i)
  have hθ' : Function.Injective θ' := (FaithfulSMul.algebraMap_injective K L).comp hθ
  let I := rowIdeal (pencilBase θ' A)
  let q := Ideal.Quotient.mkₐ L I
  have : Module.Finite L (L[X][X] ⧸ I) := finite_row_quotient θ' hθ' A hk
  let b := rowBasis θ' hθ' A hk
  let e := Fintype.equivFin (PlaneIndex (k-1))
  let b' := b.reindex e
  let r : Fin (Fintype.card (PlaneIndex (k-1))) → ℕ := fun i => (e.symm i).val.1.val
  let s : Fin (Fintype.card (PlaneIndex (k-1))) → ℕ :=
    fun i => (e.symm i).val.2.val-(e.symm i).val.1.val-1
  have hb' : ∀ i, b' i = q (monomial (r i) (monomial (s i) 1)) := by
    intro i
    exact (b.reindex_apply e i).trans (rowBasis_apply θ' hθ' A hk (e.symm i))
  have hpq : q (Bivariate.map (algebraMap K L) p) = 0 := by
    rw [← hdet]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (determinant_mem_rowIdeal θ' A)
  obtain ⟨F,hF,hmon⟩ := Bivariate.quotient_field_bound p hp q
    (Ideal.Quotient.mkₐ_surjective L I) hpq b' r s hb'
  have hmon' : ∀ a d i, b.repr (q (monomial a (monomial d 1))) i ∈ F := by
    intro a d i
    have h := hmon a d (e i)
    simpa only [b',Basis.repr_reindex_apply,Equiv.symm_apply_apply] using h
  refine ⟨F,?_,?_⟩
  · rw [row_quotient_finrank θ' hθ' A hk] at hF
    exact hF
  · apply matrix_inField_of_rows F θ' hθ' A
    · intro i
      exact F.algebraMap_mem (θ i)
    · rw [hdet]
      exact Bivariate.inField_map F p
    · exact rowEntry_inField F θ' hθ' A hk (fun i => F.algebraMap_mem (θ i)) hmon'

end PermanentBorder.DeterminantFibers

namespace PermanentBorder.AlgebraicDimension

open Order

variable {R S : Type*} [CommRing R] [CommRing S]

theorem krullDim_le_of_integral (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  apply krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J hIJ
  exact Ideal.IsIntegral.comap_lt_comap (R := R) hIJ

universe u

end PermanentBorder.AlgebraicDimension

namespace PermanentBorder.AlgebraicDimension
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

theorem krullDim_le_of_field_images [Algebra.FiniteType K A] (n : ℕ)
    (h : ∀ (L : Type u) [Field L] [Algebra K L] (f : A →ₐ[K] L),
      Algebra.trdeg K f.range ≤ (n : Cardinal)) :
    ringKrullDim A ≤ n := by
  nontriviality A
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hint⟩
  have hg' : (⊥ : Ideal A).comap (algebraMap R A) ≤ (⊥ : Ideal R) := by
    rw [← RingHom.ker_eq_comap_bot]
    exact le_of_eq ((RingHom.injective_iff_ker_eq_bot _).mp hg)
  obtain ⟨q, _, hq, hq0⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (⊥ : Ideal R) (⊥ : Ideal A) hg'
  let : q.IsPrime := hq
  let L := FractionRing (A ⧸ q)
  let f : A →ₐ[K] L := (IsScalarTower.toAlgHom K (A ⧸ q) L).comp (Ideal.Quotient.mkₐ K q)
  have hqgi : Function.Injective ((Ideal.Quotient.mk q).comp g.toRingHom) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    change (⊥ : Ideal (A ⧸ q)).comap ((Ideal.Quotient.mk q).comp g.toRingHom) = ⊥
    rw [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hq0
  have hfg : Function.Injective (f.comp g) :=
    (IsFractionRing.injective (A ⧸ q) L).comp hqgi
  have hrg : Function.Injective (f.rangeRestrict.comp g) := by
    intro x y he
    exact hfg (congrArg Subtype.val he)
  have hs : s ≤ n := by
    have hc := (trdeg_le_of_injective (f.rangeRestrict.comp g) hrg).trans (h L f)
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast,
      Nat.cast_le] using hc
  calc
    ringKrullDim A ≤ ringKrullDim R := krullDim_le_of_integral g.toRingHom hint
    _ = s := by simp [R]
    _ ≤ n := by exact_mod_cast hs

end PermanentBorder.AlgebraicDimension

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.FiberDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.DeterminantFiberScheme
open Polynomial
universe u
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem determinant_ne_zero [Nontrivial R] (θ : Fin n → R)
    (A : Matrix (Fin n) (Fin n) R) : (pencil θ A).det ≠ 0 := by
  have hc : (pencil θ A).det.coeff n = 1 := by
    have hm : (1 : Matrix (Fin n) (Fin n) R[X]).map C = 1 := C.mapMatrix.map_one
    simpa only [pencil, hm, Fintype.card_fin, Matrix.det_one] using
      coeff_det_X_add_C_card (1 : Matrix (Fin n) (Fin n) R[X])
        ((X : R[X]) • (Matrix.diagonal θ).map C + A.map C)
  intro hz
  rw [hz, coeff_zero] at hc
  exact zero_ne_one hc

variable (K : Type u) [Field K]

variable {K}

theorem range_le_of_variables_mem {σ : Type*} {L : Type u} [Field L] [Algebra K L]
    (f : MvPolynomial σ K →ₐ[K] L) (F : IntermediateField K L)
    (h : ∀ i, f (MvPolynomial.X i) ∈ F) : f.range ≤ F.toSubalgebra := by
  rintro y ⟨p, rfl⟩
  change f p ∈ F
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.algHom_C] using F.algebraMap_mem c
  | add p q hp hq => simpa only [map_add] using F.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul] using F.mul_mem hp (h i)

end PermanentBorder.DeterminantFiberScheme

namespace PermanentBorder.DeterminantFibers
open Polynomial AdjugateAlgebra
universe u
variable {K L : Type u} [Field K] [Infinite K] [Field L] [Algebra K L]
  [IsAlgClosed L] {k : ℕ}

omit [Infinite K] [IsAlgClosed L] in
lemma coefficient_mem_curveCoefficientField (P : L[X][X]) (a b : ℕ) :
    (P.coeff a).coeff b ∈ curveCoefficientField (K := K) P :=
  IntermediateField.subset_adjoin K _ (Set.mem_range_self (a,b))

theorem matrix_field_bound_over_curve (θ : Fin (k+1) → K)
    (hθ : Function.Injective θ) (A : Matrix (Fin (k+1)) (Fin (k+1)) L)
    (hk : 0 < k) (B : ℕ)
    (hB : Algebra.trdeg K (curveCoefficientField (K := K)
      (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det) ≤ (B : Cardinal)) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (B + (k+1).choose 2 : ℕ) ∧ ∀ i j, A i j ∈ F := by
  classical
  let P := (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det
  let E := curveCoefficientField (K := K) P
  let : Infinite E := Infinite.of_injective (algebraMap K E) (algebraMap K E).injective
  obtain ⟨p,hp⟩ := (Bivariate.inField_iff_lifts E P).mp
    (coefficient_mem_curveCoefficientField P)
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hp
    exact DeterminantFiberScheme.determinant_ne_zero _ _ hp.symm
  let θE : Fin (k+1) → E := fun i => algebraMap K E (θ i)
  have hθE : Function.Injective θE := (algebraMap K E).injective.comp hθ
  have hdet : (pencilMatrix (pencilBase (fun i => algebraMap E L (θE i)) A)).det =
      Bivariate.map (algebraMap E L) p := by
    exact hp.symm
  obtain ⟨F,hF,hAF⟩ := matrix_field_bound θE hθE A hk p hp0 hdet
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FaithfulSMul E F := (faithfulSMul_iff_algebraMap_injective E F).mpr
    (algebraMap E F).injective
  refine ⟨F.restrictScalars K, ?_, hAF⟩
  change Algebra.trdeg K F ≤ _
  rw [← trdeg_add_eq K E]
  exact (add_le_add hB hF).trans_eq (by simp)

end PermanentBorder.DeterminantFibers

namespace PermanentBorder.SpectralDimension
open MvPolynomial Polynomial Matrix
open Conductor AdjugateAlgebra DeterminantFibers
universe u

variable (K : Type u) [Field K]

variable {K}

theorem field_point_critical {L : Type u} [Field L] [Algebra K L] {k q : ℕ}
    (θ : Fin (k+1) → K)
    (f : (MvPolynomial (Fin (k+1) × Fin (k+1)) K ⧸ gradientIdeal K θ q) →ₐ[K] L) :
    let g := f.comp (Ideal.Quotient.mkₐ K (gradientIdeal K θ q))
    ∀ ij, MvPolynomial.eval (fun ab => g (MvPolynomial.X (ab.1,ab.2)))
      (pderiv ij (Selector.diagonalCoefficient
        (Matrix.of fun a b => (MvPolynomial.X (a,b) :
          MvPolynomial (Fin (k+1) × Fin (k+1)) L))
        (fun i => MvPolynomial.C (algebraMap K L (θ i))) q)) = 0 := by
  classical
  intro g ij
  let P := Selector.diagonalCoefficient
    (Matrix.of fun a b => (MvPolynomial.X (a,b) :
      MvPolynomial (Fin (k+1) × Fin (k+1)) K)) (fun i => MvPolynomial.C (θ i)) q
  have hP : MvPolynomial.map (algebraMap K L) P = Selector.diagonalCoefficient
      (Matrix.of fun a b => (MvPolynomial.X (a,b) :
        MvPolynomial (Fin (k+1) × Fin (k+1)) L))
      (fun i => MvPolynomial.C (algebraMap K L (θ i))) q := by
    dsimp [P]
    rw [Selector.diagonalCoefficient_map]
    simp only [Matrix.of_apply, MvPolynomial.map_X, MvPolynomial.map_C]
    rfl
  rw [← hP, MvPolynomial.pderiv_map, MvPolynomial.eval_map]
  have hg : MvPolynomial.aeval (fun ab => g (MvPolynomial.X (ab.1,ab.2))) = g := by
    ext ab
    simp only [MvPolynomial.aeval_X, Prod.mk.eta]
  change MvPolynomial.aeval _ (pderiv ij P) = 0
  rw [hg]
  change f (Ideal.Quotient.mk _ (pderiv ij P)) = 0
  have hm : pderiv ij P ∈ gradientIdeal K θ q :=
    Ideal.subset_span (Set.mem_range_self ij)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]

end PermanentBorder.SpectralDimension

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SpectralDimension
open MvPolynomial Polynomial Matrix
open Conductor AdjugateAlgebra DeterminantFibers
universe u

lemma effective_matrix_budget {k n T : ℕ} (h : 18*n+T ≤ 9*((k+1)*(k+2))) :
    n+(k+1).choose 2 ≤ (k+1)^2-T/18 := by
  have hc : 2*((k+1).choose 2)=(k+1)*k := by
    have heven : 2 ∣ (k+1)*k := by simpa [mul_comm] using (Nat.even_mul_succ_self k).two_dvd
    rw [Nat.choose_two_right,Nat.add_sub_cancel,Nat.mul_div_cancel' heven]
  have hdiv := Nat.div_mul_le_self T 18
  have hsum : n+(k+1).choose 2+T/18 ≤ (k+1)^2 := by nlinarith
  omega

theorem critical_dimension_effective {K : Type u} [Field K] [Infinite K]
    [CharP K 2] [PerfectRing K 2] {k q : ℕ} (hk : 4 ≤ k+1) (hq : 3*q ≤ k)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ) :
    ringKrullDim (MvPolynomial (Fin (k+1) × Fin (k+1)) K ⧸ gradientIdeal K θ q) ≤
      (((k+1)^2-(q+2).choose 2/18 : ℕ) : WithBot ℕ∞) := by
  classical
  apply AlgebraicDimension.krullDim_le_of_field_images (K := K)
  intro L _ _ f
  let Ω := AlgebraicClosure L
  let : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let ι : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  let f' := ι.comp f
  let g := f'.comp (Ideal.Quotient.mkₐ K (gradientIdeal K θ q))
  let A : Matrix (Fin (k+1)) (Fin (k+1)) Ω := fun a b => g (MvPolynomial.X (a,b))
  have hc := field_point_critical θ f'
  have hθΩ : Function.Injective (fun i => algebraMap K Ω (θ i)) :=
    (algebraMap K Ω).injective.comp hθ
  have hd : ((q+2).choose 2 : ℕ∞) ≤
      normalizationDefect (fun i => algebraMap K Ω (θ i)) A :=
    Selector.gradient_forces_normalization_defect hq _ hθΩ A hc
  obtain ⟨n,hn,hnum⟩ := spectral_effective_bound hk θ hθ A ((q+2).choose 2) hd
  obtain ⟨F,hF,hAF⟩ := matrix_field_bound_over_curve θ hθ A (by omega) n hn
  have hg : g.range ≤ F.toSubalgebra := by
    apply DeterminantFiberScheme.range_le_of_variables_mem
    rintro ⟨i,j⟩
    exact hAF i j
  let h : f.range →ₐ[K] Ω := ι.comp f.range.val
  have hmem : ∀ z, h z ∈ F.toSubalgebra := by
    rintro ⟨z,x,hx⟩
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    apply hg
    exact ⟨p, congrArg ι hx⟩
  let hFmap := h.codRestrict F.toSubalgebra hmem
  have hinj : Function.Injective hFmap := by
    intro x y heq
    apply Subtype.ext
    exact (FaithfulSMul.algebraMap_injective L Ω) (congrArg Subtype.val heq)
  refine ((trdeg_le_of_injective hFmap hinj).trans hF).trans ?_
  exact_mod_cast effective_matrix_budget hnum

end PermanentBorder.SpectralDimension

namespace PermanentBorder
open Parameters EffectiveParameters SpectralDimension MvPolynomial

theorem exists_effective_critical_bound_oai {K : Type} [Field K] [Infinite K]
    [CharP K 2] [PerfectRing K 2] {d : ℕ} (hd : 128 ≤ d) :
    ∃ θ : Fin d → K,
      ringKrullDim (MvPolynomial (Variables d) K ⧸
        Ideal.span (Set.range (fun i => pderiv i
          (Selector.diagonalCoefficient
            (Matrix.of fun a b => (X (a,b) : MvPolynomial (Variables d) K))
            (fun i => C (θ i)) (selectorIndex d))))) ≤
        ((d^2-sectionSize d : ℕ) : WithBot ℕ∞) := by
  classical
  cases d with
  | zero => omega
  | succ k =>
    let θ : Fin (k+1) → K := fun i => Infinite.natEmbedding K i.val
    have hθ : Function.Injective θ := by
      intro i j hij
      exact Fin.ext ((Infinite.natEmbedding K).injective hij)
    have hq : 3*selectorIndex (k+1) ≤ k := by dsimp [selectorIndex]; omega
    exact ⟨θ,critical_dimension_effective (by omega) hq θ hθ⟩

end PermanentBorder

end OAI
end

theorem solution : type_of% @OAI.PermanentBorder.exists_effective_critical_bound_oai := @OAI.PermanentBorder.exists_effective_critical_bound_oai
