-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ce9467f1-a6a7-5be4-b607-84264e7109f8

import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_ModularCurve_HeckeAlgebraHom
import Theorems.Thm_HeckeEis_exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot
import Theorems.Thm_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
import Theorems.Thm_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible
import Theorems.Thm_CuspForm_finiteDimensional_adjoin_qCoeff
import Theorems.Thm_CuspidalType_IsCuspidalOfType_exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map
import Theorems.Thm_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero
import Theorems.Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange
import Theorems.Thm_HeckeEis_isEigensystemH1_residueField_of_isEigensystemH1_of_isDiscreteValuationRing
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree"
p2m_attr_erase "simp" "Deformation.matrixRepresentation_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
open CongruenceSubgroup Polynomial
open Matrix

namespace PackBody

private theorem exists_eq_smul_of_sub_mem_pk {R G Λ : Type} [CommRing R] [Group G] [AddCommGroup Λ] [Module R Λ]
    (ρ : Representation R G Λ) (u : G) (n : ℕ) (hn : IsUnit (n : R)) (hu : ρ u ^ n = 1)
    (hinv : ∀ v : Λ, ρ u v = v → v = 0) (ϖ : R) (v w : Λ) (hv : ρ u v = v + ϖ • w) :
    ∃ v' : Λ, v = ϖ • v' := by

  have hit : ∀ i : ℕ, ∃ wi : Λ, (ρ u ^ i) v = v + ϖ • wi := by
    intro i
    induction i with
    | zero => exact ⟨0, by simp⟩
    | succ i ih =>
      obtain ⟨wi, hwi⟩ := ih
      refine ⟨w + ρ u wi, ?_⟩
      rw [pow_succ', Module.End.mul_apply, hwi, map_add, map_smul, hv, smul_add, add_assoc]
  choose wi hwi using hit

  have hfix : ρ u (∑ i ∈ Finset.range n, (ρ u ^ i) v) = ∑ i ∈ Finset.range n, (ρ u ^ i) v := by
    rw [map_sum]
    have h1 : ∀ i, ρ u ((ρ u ^ i) v) = (ρ u ^ (i + 1)) v := fun i => by rw [pow_succ', Module.End.mul_apply]
    simp_rw [h1]
    cases n with
    | zero => simp
    | succ k => rw [Finset.sum_range_succ, Finset.sum_range_succ', hu, pow_zero]
  have hzero := hinv _ hfix
  have hsum : ∑ i ∈ Finset.range n, (ρ u ^ i) v = (n : R) • v + ϖ • ∑ i ∈ Finset.range n, wi i := by
    simp_rw [hwi]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.smul_sum, Nat.cast_smul_eq_nsmul]
  rw [hsum] at hzero
  obtain ⟨m, hm⟩ := hn.exists_left_inv
  refine ⟨-(m • ∑ i ∈ Finset.range n, wi i), ?_⟩
  have h := congrArg (fun x => m • x) hzero
  simp only [smul_add, smul_zero, ← mul_smul, hm, one_smul] at h
  rw [eq_neg_of_add_eq_zero_left h, mul_comm, mul_smul, smul_neg]

private theorem exists_coboundary_of_smul_pk {R G Λ : Type} [CommRing R] [Group G] [AddCommGroup Λ] [Module R Λ]
    [NoZeroSMulDivisors R Λ] (ρ : Representation R G Λ) (u : G) (n : ℕ) (hn : IsUnit (n : R)) (hu : ρ u ^ n = 1)
    (hinv : ∀ v : Λ, ρ u v = v → v = 0) (ϖ : R) (hϖ : ϖ ≠ 0) (z : G → Λ)
    (hz : ∃ v : Λ, ∀ g : G, ϖ • z g = ρ g v - v) : ∃ v' : Λ, ∀ g : G, z g = ρ g v' - v' := by
  obtain ⟨v, hv⟩ := hz
  obtain ⟨v', rfl⟩ := exists_eq_smul_of_sub_mem_pk ρ u n hn hu hinv ϖ v (z u)
    (by rw [add_comm, ← sub_eq_iff_eq_add, ← hv u])
  refine ⟨v', fun g => sub_eq_zero.mp ((NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero ?_).resolve_left hϖ)⟩
  rw [smul_sub, hv g, map_smul, smul_sub, sub_self]

private theorem eq_zero_of_smul_coeffH1_pk {R Λ : Type} [CommRing R] [AddCommGroup Λ] [Module R Λ]
    [NoZeroSMulDivisors R Λ] (N : ℕ) (ρ : Representation R (Gamma0 N) Λ) (u : Gamma0 N) (n : ℕ)
    (hn : IsUnit (n : R)) (hu : ρ u ^ n = 1) (hinv : ∀ v : Λ, ρ u v = v → v = 0) (ϖ : R) (hϖ : ϖ ≠ 0)
    (x : HeckeEis.coeffH1 ρ) (hx : ϖ • x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := HeckeEis.coeffH1Mk_surjective ρ x
  rw [← map_smul, HeckeEis.coeffH1Mk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff] at hx
  obtain ⟨v, hv⟩ := hx
  rw [HeckeEis.coeffH1Mk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff]
  obtain ⟨v', hv'⟩ := exists_coboundary_of_smul_pk ρ u n hn hu hinv ϖ hϖ z
    ⟨v, fun g => by
      have h := congrFun hv g
      simp only [Submodule.coe_smul, Pi.smul_apply] at h
      exact h.symm⟩
  exact ⟨v', funext fun g => (hv' g).symm⟩

private theorem exists_isCoeffHeckeOnH1_pk (N ℓ : ℕ) [NeZero ℓ] {K : Type} [CommRing K] {V : Type}
    [AddCommGroup V] [Module K V] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ), a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a) :
    ∃ T : HeckeEis.coeffH1 ρ →ₗ[K] HeckeEis.coeffH1 ρ, HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ a T := by
  let F : ↥(HeckeEis.coeffCocycles ρ) →ₗ[K] ↥(HeckeEis.coeffCocycles ρ) :=
    { toFun := fun z =>
        ⟨HeckeEis.coeffHeckeFun N ℓ ρ a z, HeckeEis.coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha z.2⟩
      map_add' := fun z w => by
        ext g
        simp only [Submodule.coe_add, HeckeEis.coeffHeckeFun_apply, Pi.add_apply, map_add,
          Finset.sum_add_distrib]
      map_smul' := fun c z => by
        ext g
        simp only [Submodule.coe_smul, HeckeEis.coeffHeckeFun_apply, Pi.smul_apply, map_smul,
          Finset.smul_sum, RingHom.id_apply] }
  refine ⟨((HeckeEis.coeffCoboundaries ρ).comap (HeckeEis.coeffCocycles ρ).subtype).mapQ
    ((HeckeEis.coeffCoboundaries ρ).comap (HeckeEis.coeffCocycles ρ).subtype) F ?_, ?_⟩
  · intro z hz
    exact HeckeEis.coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz
  · intro z
    exact ⟨F z, rfl, rfl⟩

private theorem ne_of_pow_eq_one_pk {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    {θ : (GaloisField q 2)ˣ →* ℂˣ} (hθ1 : θ ≠ 1) (hθp : ∃ n : ℕ, θ ^ p ^ n = 1) : p ≠ q := by
  rintro rfl
  obtain ⟨n, hn⟩ := hθp
  have hp : p.Prime := Fact.out
  have h1 : θ ^ (p ^ 2 - 1) = 1 := by
    ext α
    rw [MonoidHom.pow_apply, ← map_pow, ← GaloisField.card p 2 two_ne_zero, ← Nat.card_units (GaloisField p 2),
      pow_card_eq_one', map_one, MonoidHom.one_apply]
  have hcop : Nat.Coprime (p ^ n) (p ^ 2 - 1) := by
    refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hp.ne_one ?_)
    have h2 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub (dvd_pow_self p two_ne_zero) h
    rwa [Nat.sub_sub_self (Nat.one_le_pow 2 p hp.pos), Nat.dvd_one] at h2
  have := (pow_gcd_eq_one (a := θ)).mpr ⟨hn, h1⟩
  rw [hcop.gcd_eq_one, pow_one] at this
  exact hθ1 this

open scoped TensorProduct NumberField

set_option backward.isDefEq.respectTransparency false in

private theorem exists_basis_repr_mem_range_pk {k K G W : Type} [Field k] [IsAlgClosed k] [Field K]
    [Algebra k K] [Group G] [Fintype G] [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]
    [FiniteDimensional K W] (ρ : Representation K G W) [hirr : ρ.IsIrreducible] :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) K W),
      ∀ (g : G) (i j : Fin d), b.repr (ρ g (b j)) i ∈ Set.range (algebraMap k K) := by
  classical

  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, w₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      (Subrepresentation.toSubmodule_injective (by
        change (⊥ : Submodule K W) = ⊤
        ext w; simp [h w]))

  let ρk : G → W →ₗ[k] W := fun g => (ρ g).restrictScalars k
  let S : Submodule k W := Submodule.span k (Set.range fun g : G => ρ g w₀)
  have hS : ∀ g : G, ∀ x ∈ S, ρk g x ∈ S := by
    intro g x hx
    refine Submodule.span_induction (fun y ⟨h, hy⟩ => ?_) (by simp) (fun y z _ _ hy hz => ?_)
      (fun c y _ hy => ?_) hx
    · exact Submodule.subset_span ⟨g * h, by simp [ρk, ← hy, map_mul]⟩
    · simpa using S.add_mem hy hz
    · simpa [ρk] using S.smul_mem c hy
  haveI : FiniteDimensional k ↥S := FiniteDimensional.span_of_finite k (Set.finite_range _)
  let τ₀ : G → ↥S →ₗ[k] ↥S := fun g => (ρk g).restrict (hS g)

  let 𝒯 : Set (Submodule k ↥S) := {T | T ≠ ⊥ ∧ ∀ g : G, ∀ x ∈ T, τ₀ g x ∈ T}
  have h𝒯 : 𝒯.Nonempty := ⟨⊤, by
    refine ⟨?_, fun g x _ => Submodule.mem_top⟩
    intro h
    have hmem : (⟨w₀, Submodule.subset_span ⟨1, by simp⟩⟩ : ↥S) ∈ (⊤ : Submodule k ↥S) := Submodule.mem_top
    rw [h, Submodule.mem_bot, Subtype.ext_iff] at hmem
    exact hw₀ hmem⟩
  obtain ⟨T₀, ⟨hT₀ne, hT₀st⟩, hT₀min⟩ := (wellFounded_lt (α := Submodule k ↥S)).has_min 𝒯 h𝒯

  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : Representation k G ↥T₀, ∀ (g : G) (x : ↥T₀), ((τ₁ g x : ↥T₀) : ↥S) = τ₀ g x :=
    ⟨{ toFun := fun g => (τ₀ g).restrict (hT₀st g)
       map_one' := by ext x; simp [τ₀, ρk]
       map_mul' := fun g h => by ext x; simp [τ₀, ρk, map_mul] }, fun g x => rfl⟩
  have hτ₀ : ∀ (g : G) (x : ↥S), ((τ₀ g x : ↥S) : W) = ρ g x := fun g x => rfl
  haveI : Nontrivial ↥T₀ := Submodule.nontrivial_iff_ne_bot.mpr hT₀ne

  haveI hT₀nt : Nontrivial (Subrepresentation τ₁) := by
    refine ⟨⟨⊥, ⊤, fun h => hT₀ne ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    change (⊥ : Submodule k ↥T₀) = ⊤ at h'
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : ↥T₀) ∈ (⊤ : Submodule k ↥T₀) := Submodule.mem_top
    rw [← h', Submodule.mem_bot, Subtype.ext_iff] at this
    exact (Submodule.mem_bot k).mpr this
  haveI hirr₁ : τ₁.IsIrreducible := by
    refine ⟨fun X => ?_⟩
    by_cases hX : X = ⊥
    · exact Or.inl hX
    refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    change X.toSubmodule = ⊤

    let T' : Submodule k ↥S := X.toSubmodule.map T₀.subtype
    have hT'le : T' ≤ T₀ := by
      rintro _ ⟨x, _, rfl⟩; exact x.2
    have hT'𝒯 : T' ∈ 𝒯 := by
      refine ⟨fun h => hX (Subrepresentation.toSubmodule_injective ?_), fun g y ⟨x, hx, hxy⟩ => ?_⟩
      · change X.toSubmodule = ⊥
        rw [eq_bot_iff]
        intro x hx
        have : T₀.subtype x ∈ T' := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact (Submodule.mem_bot k).mpr (Subtype.ext (by simpa using congrArg Subtype.val this))
      · refine ⟨τ₁ g x, X.apply_mem_toSubmodule g hx, ?_⟩
        rw [← hxy]; exact hτ₁ g x
    have hT'eq : T' = T₀ := (eq_or_lt_of_le hT'le).resolve_right (hT₀min T' hT'𝒯)
    rw [eq_top_iff]
    intro x _
    have hx : (x : ↥S) ∈ T' := by rw [hT'eq]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext (by simpa using hyx)
    exact this ▸ hy
  haveI : FiniteDimensional k ↥T₀ := inferInstance

  haveI : Representation.IsAbsolutelyIrreducible.{0} τ₁ :=
    (Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end τ₁).mpr
      ⟨hirr₁, (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2⟩

  let ι : ↥T₀ →ₗ[k] W := S.subtype ∘ₗ T₀.subtype
  have hιapp : ∀ x : ↥T₀, ι x = ((x : ↥S) : W) := fun x => rfl
  have hιinj : Function.Injective ι := fun x y h => Subtype.ext (Subtype.ext h)
  have hιG : ∀ (g : G) (x : ↥T₀), ι (τ₁ g x) = ρ g (ι x) := fun g x => by rw [hιapp, hτ₁, hτ₀, hιapp]
  have hinj := Representation.injective_liftBaseChange_of_isAbsolutelyIrreducible τ₁ ρ ι hιinj hιG

  have hsurj : Function.Surjective (ι.liftBaseChange K) := by
    let Rg : Subrepresentation ρ :=
      { toSubmodule := LinearMap.range (ι.liftBaseChange K)
        apply_mem_toSubmodule := fun g y ⟨x, hx⟩ => by
          rw [← hx]
          clear hx
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul c t => exact ⟨c ⊗ₜ τ₁ g t, by simp [hιG]⟩
          | add x y hx hy =>
            obtain ⟨x', hx'⟩ := hx; obtain ⟨y', hy'⟩ := hy
            exact ⟨x' + y', by simp [hx', hy', map_add]⟩ }
    rcases IsSimpleOrder.eq_bot_or_eq_top Rg with h | h
    · exfalso
      obtain ⟨t, ht⟩ := exists_ne (0 : ↥T₀)
      have hmem : ι.liftBaseChange K (1 ⊗ₜ t) ∈ Rg.toSubmodule := ⟨_, rfl⟩
      have h' : Rg.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
      rw [h', Submodule.mem_bot, LinearMap.liftBaseChange_tmul, one_smul] at hmem
      exact ht (hιinj (by rw [hmem, map_zero]))
    · intro w
      have hw : w ∈ Rg.toSubmodule := by
        have h' : Rg.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule h
        rw [h']; trivial
      exact hw
  let e : K ⊗[k] ↥T₀ ≃ₗ[K] W := LinearEquiv.ofBijective (ι.liftBaseChange K) ⟨hinj, hsurj⟩

  let b₀ := Module.finBasis k ↥T₀
  refine ⟨Module.finrank k ↥T₀, (Algebra.TensorProduct.basis K b₀).map e, fun g i j => ?_⟩
  have hb : ∀ j, (Algebra.TensorProduct.basis K b₀).map e j = ι (b₀ j) := fun j => by
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    change ι.liftBaseChange K (1 ⊗ₜ b₀ j) = ι (b₀ j)
    rw [LinearMap.liftBaseChange_tmul, one_smul]
  refine ⟨b₀.repr (τ₁ g (b₀ j)) i, ?_⟩
  have hsum : ρ g ((Algebra.TensorProduct.basis K b₀).map e j) =
      ∑ i, algebraMap k K (b₀.repr (τ₁ g (b₀ j)) i) • (Algebra.TensorProduct.basis K b₀).map e i := by
    simp_rw [hb, ← hιG, algebraMap_smul, ← map_smul, ← map_sum, b₀.sum_repr]
  rw [hsum, Module.Basis.repr_sum_self]

private theorem isIrreducible_dual_pk {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V)
    (hρ : ∀ U : Subrepresentation ρ, U.toSubmodule ≠ ⊥ → U.toSubmodule = ⊤) : ρ.dual.IsIrreducible := by
  haveI : Nontrivial (Subrepresentation ρ.dual) := ⟨⟨⊥, ⊤, fun h => by
    have h' : (⊥ : Submodule K (Module.Dual K V)) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule K (Module.Dual K V)) ≠ ⊤) h'⟩⟩
  refine ⟨fun X => ?_⟩

  let U : Subrepresentation ρ :=
    { toSubmodule := X.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule := fun g v hv => by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro φ hφ
        have hmem : ρ.dual g⁻¹ φ ∈ X.toSubmodule := X.apply_mem_toSubmodule g⁻¹ hφ
        have h := hv _ hmem
        rwa [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply] at h }
  by_cases hU : U.toSubmodule = ⊥
  ·
    refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    change X.toSubmodule = ⊤
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := X.toSubmodule)]
    change U.toSubmodule.dualAnnihilator = ⊤
    rw [hU, Submodule.dualAnnihilator_bot]
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    change X.toSubmodule = ⊥
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := X.toSubmodule)]
    change U.toSubmodule.dualAnnihilator = ⊥
    rw [hρ U hU, Submodule.dualAnnihilator_top]

private theorem dual_fixed_eq_zero_pk {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (u : G) (n : ℕ) (hn : (n : K) ≠ 0) (hu : u ^ n = 1)
    (hfix : ∀ v : V, ρ u v = v → v = 0) (φ : Module.Dual K V) (hφ : ρ.dual u φ = φ) : φ = 0 := by

  have hkill : ∀ v : V, φ (ρ u v) = φ v := fun v => by
    conv_lhs => rw [← hφ]
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hkill' : ∀ (i : ℕ) (v : V), φ (ρ (u ^ i) v) = φ v := fun i => by
    induction i with
    | zero => intro v; simp
    | succ i ih => intro v; rw [pow_succ, map_mul, Module.End.mul_apply, ih, hkill]

  ext v
  have havg : ∑ i ∈ Finset.range n, ρ (u ^ i) v = 0 := by
    refine hfix _ ?_
    rw [map_sum]
    have h1 : ∀ i, ρ u (ρ (u ^ i) v) = ρ (u ^ (i + 1)) v := fun i => by
      rw [pow_succ', map_mul, Module.End.mul_apply]
    simp_rw [h1]
    cases n with
    | zero => simp
    | succ k => rw [Finset.sum_range_succ, Finset.sum_range_succ', hu, pow_zero]
  have hsum : ∑ i ∈ Finset.range n, φ (ρ (u ^ i) v) = (n : K) * φ v := by
    simp_rw [hkill']
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← map_sum, havg, map_zero] at hsum
  rw [LinearMap.zero_apply]
  exact (mul_eq_zero.mp hsum.symm).resolve_left hn

private theorem exists_dvr_pk (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ ↥F] (p : ℕ) [Fact p.Prime]
    {κ : Type} [Field κ] [CharP κ p] (red𝔪 : integralClosure ℤ ℂ →+* κ) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsPrincipalIdealRing R) (_ : IsLocalRing R)
      (_ : IsDiscreteValuationRing R) (iR : R →+* ℂ)
      (fR : R →+* κ) (ϖ : R), Function.Injective iR ∧ ϖ ≠ 0 ∧ fR ϖ = 0 ∧ (∀ x : R, fR x ≠ 0 → IsUnit x) ∧
      (∀ x : R, ¬ IsUnit x → ∃ y : R, x = ϖ * y) ∧
      (∀ x : ℂ, x ∈ F → ∃ r s : R, s ≠ 0 ∧ iR s * x = iR r) ∧
      (∀ (x : R) (c : integralClosure ℤ ℂ), iR x = c → fR x = red𝔪 c) ∧
      (∀ x : R, x ≠ 0 → ∃ (m : ℕ) (u : R), IsUnit u ∧ x = ϖ ^ m * u) ∧
      (∀ x : ℂ, x ∈ F → IsIntegral ℤ x → ∃ r : R, iR r = x) ∧ (∀ r : R, iR r ∈ F) ∧
      (Ideal.span {ϖ}).IsMaximal := by
  classical
  haveI : NumberField ↥F := @NumberField.mk _ _ inferInstance inferInstance

  let g : 𝓞 F →+* ℂ := (algebraMap ↥F ℂ).comp (algebraMap (𝓞 F) ↥F)
  have hg : Function.Injective g :=
    (algebraMap ↥F ℂ).injective.comp (FaithfulSMul.algebraMap_injective (𝓞 F) ↥F)
  have hgint : ∀ x : 𝓞 F, g x ∈ integralClosure ℤ ℂ := fun x =>
    (NumberField.RingOfIntegers.isIntegral_coe x).map (algebraMap ↥F ℂ).toIntAlgHom
  let φ : 𝓞 F →+* integralClosure ℤ ℂ := g.codRestrict (integralClosure ℤ ℂ) hgint
  have hφ : ∀ x : 𝓞 F, ((φ x : integralClosure ℤ ℂ) : ℂ) = g x := fun x => rfl

  let P : Ideal (𝓞 F) := RingHom.ker (red𝔪.comp φ)
  haveI hP : P.IsPrime := RingHom.ker_isPrime _
  have hp : p.Prime := Fact.out
  have hpP : (p : 𝓞 F) ∈ P := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hPne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)

  let R := Localization.AtPrime P
  haveI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) hPne R
  have hunit : ∀ y : P.primeCompl, IsUnit (g y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h => y.2 (by
      have : (y : 𝓞 F) = 0 := hg (by rw [h, map_zero])
      rw [this]; exact P.zero_mem)
  have hunit' : ∀ y : P.primeCompl, IsUnit ((red𝔪.comp φ) y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h => y.2 h
  let iR : R →+* ℂ := IsLocalization.lift (M := P.primeCompl) hunit
  let fR : R →+* κ := IsLocalization.lift (M := P.primeCompl) hunit'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hfR : ∀ x : R, fR x ≠ 0 → IsUnit x := by
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
    refine (IsLocalization.AtPrime.isUnit_mk'_iff R P a s).mpr fun ha => hx ?_
    rw [IsLocalization.lift_mk'_spec, RingHom.mem_ker.mp ha, zero_eq_mul]
    exact Or.inr rfl
  have hiRF : ∀ r : R, iR r ∈ F := by
    intro r
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl r
    have hs : g s ≠ 0 := (hunit s).ne_zero
    have h1 : iR (IsLocalization.mk' R a s) * g s = g a := by
      rw [← IsLocalization.lift_eq (S := R) hunit (s : 𝓞 F), ← map_mul, IsLocalization.mk'_spec]
      exact IsLocalization.lift_eq hunit a
    rw [← eq_div_iff hs] at h1
    rw [h1]
    exact div_mem (algebraMap (𝓞 F) ↥F a).2 (algebraMap (𝓞 F) ↥F (s : 𝓞 F)).2
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, iR, fR, ϖ, ?_, hϖ.ne_zero, ?_,
    hfR, ?_, ?_, ?_, ?_, ?_, hiRF, ?_⟩
  ·
    refine (IsLocalization.lift_injective_iff (M := P.primeCompl) hunit).mpr fun x y => ⟨fun h => ?_, fun h => ?_⟩
    · rw [IsLocalization.injective R P.primeCompl_le_nonZeroDivisors h]
    · rw [hg h]
  ·
    by_contra h
    exact hϖ.not_isUnit (hfR ϖ h)
  ·
    intro x hx
    have hmem : x ∈ IsLocalRing.maximalIdeal R := hx
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
    obtain ⟨y, rfl⟩ := hmem
    exact ⟨y, mul_comm y ϖ⟩
  ·
    intro x hx
    obtain ⟨a, s, has⟩ := IsLocalization.exists_mk'_eq (S := ↥F) (nonZeroDivisors (𝓞 F)) (⟨x, hx⟩ : ↥F)
    refine ⟨algebraMap (𝓞 F) R a, algebraMap (𝓞 F) R s, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsLocalization.injective R P.primeCompl_le_nonZeroDivisors)).mpr
        (nonZeroDivisors.ne_zero s.2)
    · rw [IsLocalization.lift_eq, IsLocalization.lift_eq]
      have h := IsLocalization.mk'_spec' ↥F a s
      rw [has] at h
      have h' := congrArg (algebraMap ↥F ℂ) h
      rw [map_mul] at h'
      exact h'
  ·
    intro x c hxc
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
    have hs : red𝔪 (φ s) ≠ 0 := fun h => s.2 h
    have hcomp : ∀ y : 𝓞 F, (red𝔪.comp φ) y = red𝔪 (φ y) := fun y => rfl
    have h1 : iR (IsLocalization.mk' R a s) * g s = g a := by
      rw [← IsLocalization.lift_eq (S := R) hunit (s : 𝓞 F), ← map_mul, IsLocalization.mk'_spec]
      exact IsLocalization.lift_eq hunit a
    rw [hxc] at h1
    have h2 : c * φ s = φ a := Subtype.ext (by rw [Subalgebra.coe_mul, hφ, hφ]; exact h1)
    have h3 : fR (IsLocalization.mk' R a s) * red𝔪 (φ s) = red𝔪 (φ a) := by
      rw [← hcomp, ← hcomp, ← IsLocalization.lift_eq (S := R) hunit' (s : 𝓞 F), ← map_mul,
        IsLocalization.mk'_spec]
      exact IsLocalization.lift_eq hunit' a
    rw [← h2, map_mul] at h3
    exact mul_right_cancel₀ hs h3
  ·
    intro x hx
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    exact ⟨n, u, u.isUnit, by rw [hu, mul_comm]⟩
  ·
    intro x hx hint
    have hint' : IsIntegral ℤ (⟨x, hx⟩ : ↥F) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ↥F ℂ) (algebraMap ↥F ℂ).injective).mp hint
    refine ⟨algebraMap (𝓞 F) R ⟨⟨x, hx⟩, hint'⟩, ?_⟩
    rw [IsLocalization.lift_eq]
    rfl
  ·
    rw [← hϖ.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal.isMaximal R

private theorem exists_lattice_pk {R K G W : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K]
    [Algebra R K] (hRK : Function.Injective (algebraMap R K)) [Group G] [Fintype G] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (ρ : Representation K G W) {d : ℕ} (b : Module.Basis (Fin d) K W)
    (hb : ∀ (g : G) (i j : Fin d), ∃ r s : R, s ≠ 0 ∧ algebraMap R K s * b.repr (ρ g (b j)) i = algebraMap R K r) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module R Λ) (_ : Module.IsTorsionFree R Λ)
      (ρR : Representation R G Λ) (ι : Λ →+ W) (bΛ : Module.Basis (Fin d) R Λ) (bV : Module.Basis (Fin d) K W),
      Function.Injective ι ∧ (∀ (c : R) (x : Λ), ι (c • x) = algebraMap R K c • ι x) ∧
      (∀ (g : G) (x : Λ), ι (ρR g x) = ρ g (ι x)) ∧ (∀ j, bV j = ι (bΛ j)) := by
  classical

  letI : Module R W := Module.compHom W (algebraMap R K)
  have hsmul : ∀ (c : R) (w : W), c • w = algebraMap R K c • w := fun c w => rfl
  haveI : IsScalarTower R K W := ⟨fun r c w => by rw [hsmul, Algebra.smul_def, mul_smul]⟩
  haveI : Module.IsTorsionFree R W := Module.IsTorsionFree.of_smul_eq_zero fun r w h => by
    rw [hsmul, smul_eq_zero] at h
    exact h.imp_left fun h' => hRK (by rw [h', map_zero])

  let Λ₀ : Submodule R W := Submodule.span R (Set.range fun p : G × Fin d => ρ p.1 (b p.2))
  have hbmem : ∀ j, b j ∈ Λ₀ := fun j => Submodule.subset_span ⟨(1, j), by simp⟩
  have hst : ∀ g : G, ∀ x ∈ Λ₀, ((ρ g).restrictScalars R) x ∈ Λ₀ := by
    intro g x hx
    refine Submodule.span_induction (fun y ⟨p, hy⟩ => ?_) (by simp) (fun y z _ _ hy hz => ?_)
      (fun c y _ hy => ?_) hx
    · exact Submodule.subset_span ⟨(g * p.1, p.2), by simp [← hy, map_mul]⟩
    · simpa using Λ₀.add_mem hy hz
    · simpa using Λ₀.smul_mem c hy
  obtain ⟨ρR, hρR⟩ : ∃ ρR : Representation R G ↥Λ₀, ∀ (g : G) (x : ↥Λ₀), ((ρR g x : ↥Λ₀) : W) = ρ g x :=
    ⟨{ toFun := fun g => ((ρ g).restrictScalars R).restrict (hst g)
       map_one' := by ext x; simp
       map_mul' := fun g h => by ext x; simp [map_mul] }, fun g x => rfl⟩
  haveI : Module.Finite R ↥Λ₀ := Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range _))
  haveI : Module.IsTorsionFree R ↥Λ₀ := Subtype.val_injective.moduleIsTorsionFree _ fun _ _ => rfl
  haveI : Module.Free R ↥Λ₀ := Module.free_of_finite_type_torsion_free'

  have hli : LinearIndependent R fun j => (⟨b j, hbmem j⟩ : ↥Λ₀) := by
    refine LinearIndependent.of_comp Λ₀.subtype ?_
    exact (b.linearIndependent.restrict_scalars (by
      intro r s h
      exact hRK (by simpa [Algebra.smul_def] using h)))
  have hd : d ≤ Module.finrank R ↥Λ₀ := by simpa using hli.fintype_card_le_finrank

  choose r s hs hrs using hb
  let D : R := ∏ p : G × Fin d × Fin d, s p.1 p.2.1 p.2.2
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hs _ _ _
  have hcoord : ∀ x ∈ Λ₀, ∀ i : Fin d, ∃ t : R, b.repr (D • x) i = algebraMap R K t := by
    intro x hx i
    refine Submodule.span_induction (fun y ⟨p, hy⟩ => ?_) ⟨0, by simp⟩ (fun y z _ _ ⟨t, ht⟩ ⟨t', ht'⟩ => ?_)
      (fun c y _ ⟨t, ht⟩ => ?_) hx
    · obtain ⟨E, hE⟩ : s p.1 i p.2 ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ (p.1, i, p.2))
      refine ⟨E * r p.1 i p.2, ?_⟩
      rw [← hy, hsmul, map_smul, Finsupp.smul_apply, smul_eq_mul, hE, map_mul, map_mul, ← hrs p.1 i p.2]
      ring
    · exact ⟨t + t', by rw [smul_add, map_add, Finsupp.add_apply, ht, ht', map_add]⟩
    · exact ⟨c * t, by rw [smul_comm, hsmul c, map_smul, Finsupp.smul_apply, ht, smul_eq_mul, map_mul]⟩
  choose! crd hcrd using hcoord
  let ψ : ↥Λ₀ →ₗ[R] (Fin d → R) :=
    { toFun := fun x i => crd x i
      map_add' := fun x y => by
        funext i
        apply hRK
        rw [Pi.add_apply, map_add, ← hcrd _ x.2, ← hcrd _ y.2, Submodule.coe_add, ← hcrd _ (Λ₀.add_mem x.2 y.2),
          smul_add, map_add, Finsupp.add_apply]
      map_smul' := fun c x => by
        funext i
        apply hRK
        rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, ← hcrd _ x.2, Submodule.coe_smul,
          ← hcrd _ (Λ₀.smul_mem c x.2), smul_comm, hsmul c, map_smul, Finsupp.smul_apply, smul_eq_mul] }
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h : ∀ i, b.repr (D • (x : W)) i = b.repr (D • (y : W)) i := fun i => by
      rw [hcrd _ x.2, hcrd _ y.2]
      exact congrArg (algebraMap R K) (congrFun hxy i : crd x i = crd y i)
    have h' : D • (x : W) = D • (y : W) := b.repr.injective (Finsupp.ext h)
    exact Subtype.ext ((IsRegular.of_ne_zero hD).isSMulRegular h')
  have hd' : Module.finrank R ↥Λ₀ ≤ d := by
    simpa using LinearMap.finrank_le_finrank_of_injective hψ
  have hrank : Module.finrank R ↥Λ₀ = d := le_antisymm hd' hd
  let bΛ : Module.Basis (Fin d) R ↥Λ₀ := (Module.finBasis R ↥Λ₀).reindex (finCongr hrank)

  let w : Fin d → W := fun j => (bΛ j : W)
  have hspan : ⊤ ≤ Submodule.span K (Set.range w) := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hrepr := bΛ.sum_repr ⟨b i, hbmem i⟩
    have : b i = ∑ j, algebraMap R K (bΛ.repr ⟨b i, hbmem i⟩ j) • w j := by
      conv_lhs => rw [show b i = ((⟨b i, hbmem i⟩ : ↥Λ₀) : W) from rfl, ← hrepr]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hsmul, w]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hwli : LinearIndependent K w :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by
      rw [Fintype.card_fin, Module.finrank_eq_card_basis b, Fintype.card_fin])
  refine ⟨↥Λ₀, inferInstance, inferInstance, inferInstance, ρR, Λ₀.subtype.toAddMonoidHom, bΛ,
    Module.Basis.mk hwli hspan, Subtype.val_injective, fun c x => rfl, hρR, fun j => ?_⟩
  rw [Module.Basis.mk_apply]
  rfl

private theorem unipotent_one_pow_pk (q : ℕ) [Fact q.Prime] (n : ℕ) :
    CuspidalType.unipotent q 1 ^ n = CuspidalType.unipotent q (n : ZMod q) := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CuspidalType.unipotent]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CuspidalType.unipotent, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_succ]
    exact add_comm _ _

private theorem unipotent_zero_pk (q : ℕ) [Fact q.Prime] : CuspidalType.unipotent q 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CuspidalType.unipotent]

private theorem exists_matrixRep_pk {R S G Λ : Type} [CommRing R] [CommRing S] [Group G] [AddCommGroup Λ]
    [Module R Λ] (f : R →+* S) {d : ℕ} (bΛ : Module.Basis (Fin d) R Λ) (ρ : Representation R G Λ) :
    ∃ (σ : Representation S G (Fin d → S)) (red : Λ →+ (Fin d → S)),
      (∀ g, σ g = Matrix.toLin' ((LinearMap.toMatrix bΛ bΛ (ρ g)).map f)) ∧
      (∀ (x : Λ) (i : Fin d), red x i = f (bΛ.repr x i)) ∧
      (∀ (c : R) (x : Λ), red (c • x) = f c • red x) ∧
      (∀ (g : G) (x : Λ), red (ρ g x) = σ g (red x)) := by
  classical
  let σ : Representation S G (Fin d → S) :=
    { toFun := fun g => Matrix.toLin' ((LinearMap.toMatrix bΛ bΛ (ρ g)).map f)
      map_one' := by
        rw [map_one, show (1 : Module.End R Λ) = LinearMap.id from rfl, LinearMap.toMatrix_id,
          Matrix.map_one f (map_zero f) (map_one f), Matrix.toLin'_one]
        rfl
      map_mul' := fun g h => by
        rw [map_mul, show ρ g * ρ h = (ρ g).comp (ρ h) from rfl, LinearMap.toMatrix_comp bΛ bΛ bΛ, Matrix.map_mul,
          Matrix.toLin'_mul]
        rfl }
  let red : Λ →+ (Fin d → S) :=
    { toFun := fun x i => f (bΛ.repr x i)
      map_zero' := by funext i; rw [map_zero, Finsupp.zero_apply, map_zero]; rfl
      map_add' := fun x y => by funext i; simp }
  refine ⟨σ, red, fun g => rfl, fun x i => rfl, fun c x => ?_, fun g x => ?_⟩
  · funext i
    change f (bΛ.repr (c • x) i) = f c * f (bΛ.repr x i)
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  · funext i
    change f (bΛ.repr (ρ g x) i) = Matrix.toLin' ((LinearMap.toMatrix bΛ bΛ (ρ g)).map f) (fun j => f (bΛ.repr x j)) i
    rw [Matrix.toLin'_apply, ← LinearMap.toMatrix_mulVec_repr bΛ bΛ (ρ g) x]
    simp only [mulVec, dotProduct, map_apply, map_sum, map_mul]

private theorem red_surjective_ker_pk {R S Λ : Type} [CommRing R] [CommRing S] [AddCommGroup Λ] [Module R Λ]
    (f : R →+* S) {d : ℕ} (bΛ : Module.Basis (Fin d) R Λ) (red : Λ →+ (Fin d → S))
    (hred : ∀ (x : Λ) (i : Fin d), red x i = f (bΛ.repr x i)) (ϖ : R) (hf : Function.Surjective f)
    (hker : ∀ r : R, f r = 0 ↔ ∃ s : R, r = ϖ * s) :
    Function.Surjective red ∧ ∀ x : Λ, red x = 0 ↔ ∃ y : Λ, x = ϖ • y := by
  classical
  refine ⟨fun v => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · choose r hr using fun i => hf (v i)
    refine ⟨∑ i, r i • bΛ i, funext fun i => ?_⟩
    rw [hred, bΛ.repr_sum_self, hr]
  · have hc : ∀ i, ∃ s : R, bΛ.repr x i = ϖ * s := fun i => (hker _).mp (by rw [← hred, hx]; rfl)
    choose s hs using hc
    refine ⟨∑ i, s i • bΛ i, bΛ.repr.injective (Finsupp.ext fun i => ?_)⟩
    rw [map_smul, Finsupp.smul_apply, bΛ.repr_sum_self, smul_eq_mul, hs]
  · rintro ⟨y, rfl⟩
    funext i
    rw [hred, map_smul, Finsupp.smul_apply, smul_eq_mul, Pi.zero_apply, (hker _).mpr ⟨_, rfl⟩]

private theorem charpoly_dual_pk {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K G V) (g : G) :
    LinearMap.charpoly (ρ.dual g) = LinearMap.charpoly (ρ g⁻¹) := by
  classical
  let b := Module.finBasis K V
  rw [Representation.dual_apply, ← LinearMap.charpoly_toMatrix _ b.dualBasis, LinearMap.toMatrix_transpose,
    Matrix.charpoly_transpose, LinearMap.charpoly_toMatrix]

private theorem charpoly_ofMulAction_inv_pk {k G X : Type} [Field k] [Group G] [MulAction G X] [Fintype X]
    [DecidableEq X] (g : G) :
    LinearMap.charpoly (Representation.ofMulActionFinsupp k G X g⁻¹) =
      LinearMap.charpoly (Representation.ofMulActionFinsupp k G X g) := by
  let b : Module.Basis X k (X →₀ k) := Finsupp.basisSingleOne
  have hM : ∀ (h : G) (i j : X),
      LinearMap.toMatrix b b (Representation.ofMulActionFinsupp k G X h) i j = if h • j = i then 1 else 0 := by
    intro h i j
    rw [LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne, Representation.ofMulActionFinsupp_single,
      Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Finsupp.single_apply]
  have ht : LinearMap.toMatrix b b (Representation.ofMulActionFinsupp k G X g⁻¹) =
      (LinearMap.toMatrix b b (Representation.ofMulActionFinsupp k G X g))ᵀ := by
    ext i j
    rw [Matrix.transpose_apply, hM, hM]
    exact if_congr (inv_smul_eq_iff.trans eq_comm) rfl rfl
  rw [← LinearMap.charpoly_toMatrix _ b, ht, Matrix.charpoly_transpose, LinearMap.charpoly_toMatrix]

private theorem charpoly_ofMulAction_map_pk {k k' G X : Type} [Field k] [Field k'] (j : k →+* k') [Group G]
    [MulAction G X] [Fintype X] [DecidableEq X] (g : G) :
    LinearMap.charpoly (Representation.ofMulActionFinsupp k' G X g) =
      (LinearMap.charpoly (Representation.ofMulActionFinsupp k G X g)).map j := by
  let b : Module.Basis X k (X →₀ k) := Finsupp.basisSingleOne
  let b' : Module.Basis X k' (X →₀ k') := Finsupp.basisSingleOne
  have hM : LinearMap.toMatrix b' b' (Representation.ofMulActionFinsupp k' G X g) =
      (LinearMap.toMatrix b b (Representation.ofMulActionFinsupp k G X g)).map j := by
    ext i i'
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
      Finsupp.coe_basisSingleOne, Representation.ofMulActionFinsupp_single, Representation.ofMulActionFinsupp_single,
      Finsupp.basisSingleOne_repr, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, LinearEquiv.refl_apply,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  rw [← LinearMap.charpoly_toMatrix _ b', hM, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

private theorem charpoly_toLin'_map_pk {R S : Type} [CommRing R] [CommRing S] [Nontrivial S] (f : R →+* S) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) R) :
    LinearMap.charpoly (Matrix.toLin' (A.map f)) = A.charpoly.map f := by
  rw [Matrix.charpoly_toLin', Matrix.charpoly_map]

private theorem toMatrix_eq_map_pk {R K G Λ V : Type} [CommRing R] [Field K] [Algebra R K] [Group G] [AddCommGroup Λ]
    [Module R Λ] [AddCommGroup V] [Module K V] (ρR : Representation R G Λ) (ρ : Representation K G V) (ι : Λ →+ V)
    (hιs : ∀ (c : R) (x : Λ), ι (c • x) = algebraMap R K c • ι x) (g : G) (hιρ : ∀ x : Λ, ι (ρR g x) = ρ g (ι x))
    {d : ℕ} (bΛ : Module.Basis (Fin d) R Λ) (bV : Module.Basis (Fin d) K V) (hb : ∀ j, bV j = ι (bΛ j)) :
    LinearMap.toMatrix bV bV (ρ g) = (LinearMap.toMatrix bΛ bΛ (ρR g)).map (algebraMap R K) := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb, ← hιρ]
  have h := bΛ.sum_repr (ρR g (bΛ j))
  conv_lhs => rw [← h, map_sum]
  simp_rw [hιs, ← hb]
  rw [bV.repr_sum_self]

private theorem smul_eq_zero_of_uniformizer_pk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ϖ : R)
    (hfac : ∀ r : R, r ≠ 0 → ∃ (m : ℕ) (u : R), IsUnit u ∧ r = ϖ ^ m * u) (htf : ∀ x : M, ϖ • x = 0 → x = 0)
    (c : R) (x : M) (h : c • x = 0) : c = 0 ∨ x = 0 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · obtain ⟨m, u, hu, rfl⟩ := hfac c hc
    refine Or.inr ?_
    have hpow : ∀ (n : ℕ) (y : M), ϖ ^ n • y = 0 → y = 0 := by
      intro n
      induction n with
      | zero => intro y hy; rwa [pow_zero, one_smul] at hy
      | succ n ih => intro y hy; rw [pow_succ', mul_smul] at hy; exact ih y (htf _ hy)
    have hux : u • x = 0 := hpow m (u • x) (by rwa [← mul_smul])
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    rw [← one_smul R x, ← hv, mul_smul, hux, smul_zero]

private theorem isEigensystemH1_congr_pk {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] (N : ℕ)
    (ρ : Representation K (Gamma0 N) V) (a : ℕ → (V →ₗ[K] V)) (S₀ : Set ℕ) (lam lam' : ℕ → K)
    (hlam : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = lam' ℓ) (h : HeckeEis.IsEigensystemH1 N ρ a S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ lam' := by
  obtain ⟨x, hx, hT⟩ := h
  refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT1, hT2⟩ := hT ℓ hℓ hℓN hℓS
  exact ⟨T, hT1, by rw [← hlam ℓ hℓ hℓN hℓS]; exact hT2⟩

end PackBody

open PackBody in
theorem solution
    (N : ℕ) [NeZero N] {q : ℕ} [Fact q.Prime]
    (g : CuspForm (Gamma0 (N * q ^ 2)) 2) (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (hfi : Function.Injective f)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ) (hθ : CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V))
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)
    (H₁ : Subgroup (ZMod (N * q ^ 2))ˣ)
    (hH₁ : H₁ = (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker)
    (conj : ↥red.ker →* ↥(CohCarrier.GammaH (N * q ^ 2) H₁))
    (hconj : ∀ x : ↥red.ker,
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 = ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
      (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
        (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1)
    (φ : CohCarrier.H1 (N * q ^ 2) H₁
        (Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)))
    (hφ0 : φ ≠ 0)
    (hφeq : ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker),
        φ (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) =
          (LocalNewvector.gl2ReductionRep q V).dual (red γ) (φ (Additive.ofMul (conj ⟨y, hy⟩))))
    (hφT : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ((LocalNewvector.gl2ReductionRep q V).dual
            (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))).toAddMonoidHom.comp
          (CohCarrier.heckeT (N * q ^ 2) H₁ ℓ
            (Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) φ) =
          ModularFormClass.qCoeff g ℓ • φ)
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] (𝔪 : Ideal (integralClosure ℤ ℂ))
    (red𝔪 : integralClosure ℤ ℂ →+* κ) (hker𝔪 : RingHom.ker red𝔪 = 𝔪)
    (S₀ : Set ℕ) (hqS₀ : q ∈ S₀) (b : ℕ → ℤ)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ℓ ∉ S₀ →
      ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff g ℓ ∧ c - (b ℓ : integralClosure ℤ ℂ) ∈ 𝔪)
    (hθ1 : θ ≠ 1) (hθp : ∃ n : ℕ, θ ^ p ^ n = 1)
:
    ∃ (Vσ : Type) (_ : AddCommGroup Vσ) (_ : Module κ Vσ) (_ : FiniteDimensional κ Vσ)
      (σ : Representation κ (CuspidalType.GL2 q) Vσ),
      (∀ g' : CuspidalType.GL2 q,
      LinearMap.charpoly (CuspidalType.ind q κ g') = (X - 1) ^ 2 * LinearMap.charpoly (σ g')) ∧
      HeckeEis.IsEigensystemH1 N (σ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then σ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        S₀ (fun ℓ => ((b ℓ : ℤ) : κ)) := by

  have _ := hΦg
  have _ := hf
  have _ := hfi
  have _ := hfr

  obtain ⟨Smap, hSres, hSinj, hSrange, hST⟩ :=
    HeckeEis.exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero N q ℂ
      (LocalNewvector.gl2ReductionRep q V).dual red hred H₁ hH₁ conj hconj
  obtain ⟨x, hx⟩ := (hSrange φ).mpr hφeq
  have hx0 : x ≠ 0 := fun h => hφ0 (by rw [← hx, h, map_zero])
  have hq : q.Prime := Fact.out
  have hxT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∃ (h : ((ℓ : ZMod q) ≠ 0)) (T : HeckeEis.coeffH1 ((LocalNewvector.gl2ReductionRep q V).dual.comp red) →ₗ[ℂ]
          HeckeEis.coeffH1 ((LocalNewvector.gl2ReductionRep q V).dual.comp red)),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         HeckeEis.IsCoeffHeckeOnH1 N ℓ ((LocalNewvector.gl2ReductionRep q V).dual.comp red)
          ((LocalNewvector.gl2ReductionRep q V).dual (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))) T) ∧
        T x = ModularFormClass.qCoeff g ℓ • x := by
    intro ℓ hℓ hℓN hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓq : ℓ ≠ q := fun h => hℓS (h ▸ hqS₀)
    have h : (ℓ : ZMod q) ≠ 0 := fun h0 =>
      hℓq ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp ((ZMod.natCast_eq_zero_iff ℓ q).mp h0)).symm
    have hcop : Nat.Coprime ℓ (N * q) :=
      Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN) ((Nat.coprime_primes hℓ hq).mpr hℓq)
    have hℓNq : ¬ ℓ ∣ N * q ^ 2 := fun hd =>
      (hℓ.dvd_mul.mp hd).elim hℓN fun h2 => hℓq ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp (hℓ.dvd_of_dvd_pow h2))
    obtain ⟨T, hT, hTS⟩ := hST ℓ hcop h
    refine ⟨h, T, hT, hSinj ?_⟩
    rw [hTS x, hx, map_smul, hx]
    exact hφT ℓ hℓ hℓNq h

  have hp : p.Prime := Fact.out
  have hpq : p ≠ q := ne_of_pow_eq_one_pk p hθ1 hθp
  have hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪 := by
    rw [← hker𝔪, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hq1 : (q : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hq.one_lt.ne'
  haveI : Nontrivial ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [hθ.finrank_eq]; exact Nat.sub_pos_of_lt hq.one_lt)
  haveI := isIrreducible_dual_pk (LocalNewvector.gl2ReductionRep q V) fun U hU =>
    hθ.toSubmodule_eq_top_of_ne_bot hq0 hq1 U hU

  haveI : IsAlgClosed ↥(algebraicClosure ℚ ℂ) := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  classical
  haveI : Fintype (CuspidalType.GL2 q) := Fintype.ofFinite _
  obtain ⟨d, bW, hbW⟩ :=
    exists_basis_repr_mem_range_pk (k := ↥(algebraicClosure ℚ ℂ)) (LocalNewvector.gl2ReductionRep q V).dual

  obtain ⟨F, _, hEntF, haF⟩ : ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ ↥F),
      (∀ (t : CuspidalType.GL2 q) (i j : Fin d), bW.repr ((LocalNewvector.gl2ReductionRep q V).dual t (bW j)) i ∈ F) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g n ∈ F := by
    let Ent : Set ℂ := Set.range fun t : CuspidalType.GL2 q × Fin d × Fin d =>
      bW.repr ((LocalNewvector.gl2ReductionRep q V).dual t.1 (bW t.2.2)) t.2.1
    have hEnt : ∀ x ∈ Ent, IsIntegral ℚ x := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨y, hy⟩ := hbW t.1 t.2.1 t.2.2
      change IsIntegral ℚ (bW.repr ((LocalNewvector.gl2ReductionRep q V).dual t.1 (bW t.2.2)) t.2.1)
      rw [← hy]
      exact (mem_algebraicClosure_iff.mp y.2).isIntegral
    haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ Ent) := IntermediateField.finiteDimensional_adjoin hEnt
    haveI := CuspForm.finiteDimensional_adjoin_qCoeff hg.isNormalizedEigenform
    refine ⟨IntermediateField.adjoin ℚ Ent ⊔
        IntermediateField.adjoin ℚ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n),
      inferInstance, fun t i j => ?_, fun n => ?_⟩
    · exact (le_sup_left : IntermediateField.adjoin ℚ Ent ≤ _) (IntermediateField.subset_adjoin ℚ Ent ⟨(t, i, j), rfl⟩)
    · exact (le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩)

  obtain ⟨R, _, _, _, _, _, iR, fR, ϖ, hiR, hϖ0, hfϖ, hfu, hϖdvd, hFrac, hcompat, hfac, hintR, hiRF, hϖmax⟩ :=
    exists_dvr_pk F p red𝔪
  letI : Algebra R ℂ := iR.toAlgebra

  obtain ⟨Λ, _, _, _, ρRG, ι, bΛ, bV, hιinj, hιs, hιρ, hbb⟩ :=
    exists_lattice_pk (K := ℂ) hiR (LocalNewvector.gl2ReductionRep q V).dual bW fun t i j => hFrac _ (hEntF t i j)
  haveI : NoZeroSMulDivisors R Λ := ⟨fun h => (Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance _ _ h)⟩
  let ρR : Representation R ↥(Gamma0 N) Λ := ρRG.comp red

  have hqκ : (q : κ) ≠ 0 := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp ((CharP.cast_eq_zero_iff κ p q).mp h))
  have hqunit : IsUnit (q : R) := hfu _ (by rw [map_natCast]; exact hqκ)
  let uT : ↥(Gamma0 N) := ⟨ModularGroup.T, by rw [Gamma0_mem]; simp [ModularGroup.coe_T]⟩
  have hredT : red uT = CuspidalType.unipotent q 1 := by
    rw [hred]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uT, CuspidalType.unipotent, ModularGroup.coe_T]
  have huq : CuspidalType.unipotent q (1 : ZMod q) ^ q = 1 := by
    rw [unipotent_one_pow_pk, ZMod.natCast_self, unipotent_zero_pk]
  have hu : ρR uT ^ q = 1 := by
    rw [← map_pow, show ρR (uT ^ q) = ρRG (red (uT ^ q)) from rfl, map_pow, hredT, huq, map_one]
  have hinv : ∀ v : Λ, ρR uT v = v → v = 0 := by
    intro v hv
    apply hιinj
    rw [map_zero]
    refine dual_fixed_eq_zero_pk (LocalNewvector.gl2ReductionRep q V) (CuspidalType.unipotent q 1) q hq0 huq
      (fun w hw => hθ.cuspidal w fun t => ?_) (ι v) ?_
    · rw [← ZMod.natCast_zmod_val t, ← unipotent_one_pow_pk]
      induction t.val with
      | zero => simp
      | succ k ih => rw [pow_succ, map_mul, Module.End.mul_apply, hw, ih]
    · rw [← hredT, ← hιρ]
      exact congrArg ι hv

  have htf : ∀ x : HeckeEis.coeffH1 ρR, ϖ • x = 0 → x = 0 :=
    eq_zero_of_smul_coeffH1_pk N ρR uT q hqunit hu hinv ϖ hϖ0

  obtain ⟨σ, redκ, hσ, hredκ, hredκs, hredκρ⟩ := exists_matrixRep_pk fR bΛ ρRG

  haveI : Fintype (CuspidalType.ProjLine q) := Fintype.ofFinite _
  have hpR : ¬ IsUnit (p : R) := fun hu => by
    have h := hu.map fR
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  have hϖnu : ¬ IsUnit ϖ := fun hu => by
    have h := hu.map fR
    rw [hfϖ] at h
    exact not_isUnit_zero h
  have hchar : ∀ g' : CuspidalType.GL2 q,
      LinearMap.charpoly (CuspidalType.ind q κ g') = (X - 1) ^ 2 * LinearMap.charpoly (σ g') := by
    intro g'

    obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing iR
    let iO : R →+* ↥O.toSubring := iR.codRestrict O.toSubring hO
    let resO : ↥O →+* IsLocalRing.ResidueField ↥O := IsLocalRing.residue ↥O
    have hnu : ∀ r : R, ¬ IsUnit r → resO (iO r) = 0 := fun r hr =>
      (IsLocalRing.residue_eq_zero_iff _).mpr fun hu => hr (IsLocalHom.map_nonunit r hu)
    haveI : CharP (IsLocalRing.ResidueField ↥O) p := by
      refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
      have h := hnu _ hpR
      rwa [map_natCast, map_natCast] at h
    obtain ⟨Fp, hFp1, hFp2⟩ :=
      CuspidalType.IsCuspidalOfType.exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map p hθ1 hθp hθ
        O (IsLocalRing.ResidueField ↥O) resO g'⁻¹

    have hAℂ : LinearMap.charpoly ((LocalNewvector.gl2ReductionRep q V).dual g') =
        ((LinearMap.toMatrix bΛ bΛ (ρRG g')).charpoly).map iR := by
      rw [← LinearMap.charpoly_toMatrix _ bV, toMatrix_eq_map_pk ρRG _ ι hιs g' (hιρ g') bΛ bV hbb,
        Matrix.charpoly_map]
      rfl
    have hFp : Fp = ((LinearMap.toMatrix bΛ bΛ (ρRG g')).map iO).charpoly := by
      apply Polynomial.map_injective O.subtype Subtype.val_injective
      rw [← hFp1, ← charpoly_dual_pk, hAℂ, Matrix.charpoly_map, Polynomial.map_map]
      rfl
    have hO' : LinearMap.charpoly (CuspidalType.ind q (IsLocalRing.ResidueField ↥O) g'⁻¹) =
        (X - 1) ^ 2 * ((LinearMap.toMatrix bΛ bΛ (ρRG g')).charpoly).map (resO.comp iO) := by
      rw [hFp2, hFp, Matrix.charpoly_map, Polynomial.map_map]

    haveI := hϖmax
    letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
    have hvan : ∀ r : R, r ∈ Ideal.span {ϖ} → (resO.comp iO) r = 0 := fun r hr => by
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      rw [RingHom.comp_apply, map_mul, map_mul, hnu ϖ hϖnu, mul_zero]
    have hvan' : ∀ r : R, r ∈ Ideal.span {ϖ} → fR r = 0 := fun r hr => by
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      rw [map_mul, hfϖ, mul_zero]
    let jO : R ⧸ Ideal.span {ϖ} →+* IsLocalRing.ResidueField ↥O := Ideal.Quotient.lift _ (resO.comp iO) hvan
    let jκ : R ⧸ Ideal.span {ϖ} →+* κ := Ideal.Quotient.lift _ fR hvan'
    have hjO : jO.comp (Ideal.Quotient.mk _) = resO.comp iO := Ideal.Quotient.lift_comp_mk _ _ _
    have hjκ : jκ.comp (Ideal.Quotient.mk _) = fR := Ideal.Quotient.lift_comp_mk _ _ _
    have hR' : LinearMap.charpoly (CuspidalType.ind q (R ⧸ Ideal.span {ϖ}) g') =
        (X - 1) ^ 2 * ((LinearMap.toMatrix bΛ bΛ (ρRG g')).charpoly).map (Ideal.Quotient.mk _) := by
      apply Polynomial.map_injective jO jO.injective
      rw [← charpoly_ofMulAction_map_pk jO g', ← charpoly_ofMulAction_inv_pk g', hO', Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.map_map, hjO]
    rw [charpoly_ofMulAction_map_pk jκ g', hR', Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_map, hjκ, hσ g', charpoly_toLin'_map_pk]
  refine ⟨Fin d → κ, inferInstance, inferInstance, inferInstance, σ, hchar, ?_⟩

  have hrel : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ((ℓ : ZMod q) ≠ 0) := fun ℓ hℓ hℓN hℓS h0 =>
    hℓS (((Nat.prime_dvd_prime_iff_eq hq hℓ).mp ((ZMod.natCast_eq_zero_iff ℓ q).mp h0)).symm ▸ hqS₀)

  let aO : ℕ → (Λ →ₗ[R] Λ) := fun ℓ =>
    if h : ((ℓ : ZMod q) ≠ 0) then ρRG (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id
  let aL : ℕ → (Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ]
      Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) := fun ℓ =>
    if h : ((ℓ : ZMod q) ≠ 0) then
      (LocalNewvector.gl2ReductionRep q V).dual (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))
    else LinearMap.id
  obtain ⟨σk, redk, hσk, hredk, hredks, hredkρ⟩ := exists_matrixRep_pk (IsLocalRing.residue R) bΛ ρRG
  let ak : ℕ → ((Fin d → IsLocalRing.ResidueField R) →ₗ[IsLocalRing.ResidueField R]
      (Fin d → IsLocalRing.ResidueField R)) := fun ℓ =>
    if h : ((ℓ : ZMod q) ≠ 0) then σk (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id
  have haO : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ), aO ℓ ∘ₗ ρR (HeckeEis.heckeConj N ℓ u) = ρR (u : Gamma0 N) ∘ₗ aO ℓ := by
    intro ℓ _ hℓ hℓN hℓS u
    have h := hrel ℓ hℓ hℓN hℓS
    simp only [aO, dif_pos h]
    exact HeckeEis.diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero N q R ρRG red hred ℓ h u

  let jL : Λ →ₛₗ[algebraMap R ℂ]
      Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :=
    { toFun := ι, map_add' := ι.map_add, map_smul' := hιs }
  let jk : Λ →ₛₗ[IsLocalRing.residue R] (Fin d → IsLocalRing.ResidueField R) :=
    { toFun := redk, map_add' := redk.map_add, map_smul' := hredks }
  have hbk : ∀ i : Fin d, (Pi.basisFun (IsLocalRing.ResidueField R) (Fin d)) i = jk (bΛ i) := by
    intro i
    funext j
    change (Pi.basisFun (IsLocalRing.ResidueField R) (Fin d)) i j = redk (bΛ i) j
    rw [hredk, bΛ.repr_self, Pi.basisFun_apply, Finsupp.single_apply, Pi.single_apply]
    by_cases hij : j = i
    · rw [if_pos hij, if_pos hij.symm, map_one]
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]

  have hlam : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∃ r : R, iR r = ModularFormClass.qCoeff g ℓ ∧ fR r = ((b ℓ : ℤ) : κ) := by
    intro ℓ hℓ hℓN hℓS
    have hℓq : ℓ ≠ q := fun h => hℓS (h ▸ hqS₀)
    have hℓNq : ¬ ℓ ∣ N * q ^ 2 := fun hd =>
      (hℓ.dvd_mul.mp hd).elim hℓN fun h2 => hℓq ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp (hℓ.dvd_of_dvd_pow h2))
    obtain ⟨c, hc, hcb⟩ := hcong ℓ hℓ hℓNq hℓS
    obtain ⟨r, hr⟩ := hintR _ (haF ℓ) (hc ▸ c.2)
    refine ⟨r, hr, ?_⟩
    rw [hcompat r c (hr.trans hc.symm)]
    have h0 : red𝔪 (c - (b ℓ : integralClosure ℤ ℂ)) = 0 := by
      rw [← RingHom.mem_ker, hker𝔪]
      exact hcb
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, map_intCast]
  choose! lamf hlamf using hlam

  have hL : HeckeEis.IsEigensystemH1 N ((LocalNewvector.gl2ReductionRep q V).dual.comp red) aL S₀
      (fun ℓ => algebraMap R ℂ (lamf ℓ)) := by
    refine ⟨x, hx0, fun ℓ hℓ hℓN hℓS => ?_⟩
    obtain ⟨h, T, hT, hTx⟩ := hxT ℓ hℓ hℓN hℓS
    refine ⟨T, ?_, ?_⟩
    · simp only [aL, dif_pos h]
      exact hT
    · rw [hTx]
      change ModularFormClass.qCoeff g ℓ • x = iR (lamf ℓ) • x
      rw [(hlamf ℓ hℓ hℓN hℓS).1]

  have hk : HeckeEis.IsEigensystemH1 N (σk.comp red) ak S₀ (fun ℓ => IsLocalRing.residue R (lamf ℓ)) :=
    HeckeEis.isEigensystemH1_residueField_of_isEigensystemH1_of_isDiscreteValuationRing N hiR S₀ ρR
      ((LocalNewvector.gl2ReductionRep q V).dual.comp red) (σk.comp red) aO aL ak haO jL (fun g' y => hιρ (red g') y)
      (fun ℓ y hℓ hℓN hℓS => by
        have h := hrel ℓ hℓ hℓN hℓS
        simp only [aO, aL, dif_pos h]
        exact hιρ _ y)
      jk (fun g' y => hredkρ (red g') y)
      (fun ℓ y hℓ hℓN hℓS => by
        have h := hrel ℓ hℓ hℓN hℓS
        simp only [ak, aO, dif_pos h]
        exact hredkρ _ y)
      ⟨Fin d, inferInstance, bΛ, bV, Pi.basisFun _ _, hbb, hbk⟩ (smul_eq_zero_of_uniformizer_pk ϖ hfac htf) lamf hL

  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := (IsLocalRing.eq_maximalIdeal hϖmax).symm
  let iκ : IsLocalRing.ResidueField R →+* κ :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) fR fun r hr => by
      rw [hmax] at hr
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      rw [map_mul, hfϖ, mul_zero]
  have hiκ : ∀ r : R, iκ (IsLocalRing.residue R r) = fR r := fun r => Ideal.Quotient.lift_mk _ _ _
  let jκ : (Fin d → IsLocalRing.ResidueField R) →ₛₗ[iκ] (Fin d → κ) :=
    { toFun := fun v i => iκ (v i),
      map_add' := fun v w => by funext i; exact map_add iκ (v i) (w i),
      map_smul' := fun c v => by funext i; exact map_mul iκ c (v i) }
  have hjκ : ∀ v i, jκ v i = iκ (v i) := fun v i => rfl
  have hσσ : ∀ (g' : CuspidalType.GL2 q) (v : Fin d → IsLocalRing.ResidueField R), jκ (σk g' v) = σ g' (jκ v) := by
    intro g' v
    funext i
    rw [hjκ, hσk, hσ, Matrix.toLin'_apply, Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hiκ, hjκ]
  rw [← hred]
  refine isEigensystemH1_congr_pk N (σ.comp red) _ S₀ (fun ℓ => iκ (IsLocalRing.residue R (lamf ℓ))) _
    (fun ℓ hℓ hℓN hℓS => by
      change iκ (IsLocalRing.residue R (lamf ℓ)) = ((b ℓ : ℤ) : κ)
      rw [hiκ, (hlamf ℓ hℓ hℓN hℓS).2]) ?_
  refine HeckeEis.isEigensystemH1_of_isEigensystemH1_of_isBaseChange N iκ S₀ (σk.comp red) (σ.comp red) ak _
    (fun ℓ _ hℓ hℓN hℓS u => ?_) jκ (fun g' v => hσσ (red g') v) (fun ℓ v hℓ hℓN hℓS => ?_)
    ⟨Fin d, Pi.basisFun _ _, Pi.basisFun _ _, fun i => ?_⟩ _ hk
  · have h := hrel ℓ hℓ hℓN hℓS
    simp only [dif_pos h]
    exact HeckeEis.diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero N q κ σ red hred ℓ h u
  · have h := hrel ℓ hℓ hℓN hℓS
    simp only [ak, dif_pos h]
    exact hσσ _ v
  · funext j
    rw [hjκ, Pi.basisFun_apply, Pi.basisFun_apply, Pi.single_apply, Pi.single_apply]
    by_cases hij : j = i
    · rw [if_pos hij, if_pos hij, map_one]
    · rw [if_neg hij, if_neg hij, map_zero]

end S_HeckeEis_isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr (solution)
