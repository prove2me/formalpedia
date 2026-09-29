-- Prove2me | solution 1 for ModularCurve.Period.exists_parabolicRealization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/89398323-16d2-54a1-93cb-f67d6c95246a

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_ModularCurve_HeckeAlgebraHom
import Definitions.Def_CuspForm_EigenformCoefficientRing
import Theorems.Thm_ModularCurve_periodMap_injective
import Theorems.Thm_ModularCurve_periodMap_mem_parabolicHoms
import Theorems.Thm_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform
import Theorems.Thm_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd
import Theorems.Thm_ModularCurve_Period_heckeOperatorHom_preserves_parabolic
import Theorems.Thm_ModularCurve_periodMap_add
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_exists_parabolicRealization

set_option Elab.async false
set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsParabolicHom Period.parabolicHoms Period.mem_parabolicHoms_iff periodMap periodMap_injective periodMap_mem_parabolicHoms heckeOperatorHom_periodMap_of_isNormalizedEigenform heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd periodMap_add"
namespace SpanCast
p2m_open "ModularCurve"

def castPost {G : Type*} [AddMonoid G] (L : Type*) [AddGroupWithOne L] (ψ : G →+ ℤ) : G →+ L :=
  (Int.castAddHom L).comp ψ

@[scoped simp] theorem castPost_apply {G : Type*} [AddMonoid G] (L : Type*) [AddGroupWithOne L] (ψ : G →+ ℤ)
    (g : G) : castPost L ψ g = ((ψ g : ℤ) : L) := rfl

theorem isParabolicHom_castPost {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (L : Type*)
    [CommRing L] {ψ : Additive Γ →+ ℤ} (hψ : ModularCurve.Period.IsParabolicHom Γ ψ) :
    ModularCurve.Period.IsParabolicHom Γ (castPost L ψ) := by
  intro γ hγ
  rw [castPost_apply, hψ γ hγ, Int.cast_zero]

theorem mem_span_castPost_parabolicHoms {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    [Group.FG Γ] {L : Type*} [CommRing L] [NoZeroSMulDivisors ℤ L]
    (φ : Additive Γ →+ L) (hφ : φ ∈ ModularCurve.Period.parabolicHoms L Γ L) :
    φ ∈ Submodule.span L
      ((fun ψ : ↥(ModularCurve.Period.parabolicHoms ℤ Γ ℤ) => castPost L ψ.1) '' Set.univ) := by
  classical

  let S : Submodule ℤ L := (AddMonoidHom.range φ).toIntSubmodule
  have hSfg : S.FG := by
    rw [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup,
      ← AddGroup.fg_iff_addSubgroup_fg]
    infer_instance
  haveI : Module.Finite ℤ S := Module.Finite.iff_fg.mpr hSfg
  haveI : Module.IsTorsionFree ℤ S :=
    Function.Injective.moduleIsTorsionFree (Subtype.val : S → L) Subtype.val_injective (fun _ _ => rfl)
  haveI : Module.Free ℤ S := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ S

  let ψ : Additive Γ →+ S :=
    { toFun := fun g => ⟨φ g, by
        change φ g ∈ (AddMonoidHom.range φ).toIntSubmodule
        exact ⟨g, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun x y => Subtype.ext (map_add φ x y) }
  have hψ : ∀ g, ((ψ g : S) : L) = φ g := fun _ => rfl

  let c : Module.Free.ChooseBasisIndex ℤ S → (Additive Γ →+ ℤ) :=
    fun j => (b.coord j).toAddMonoidHom.comp ψ
  have hc_apply : ∀ j g, c j g = b.repr (ψ g) j := fun _ _ => rfl
  have hc_par : ∀ j, ModularCurve.Period.IsParabolicHom Γ (c j) := by
    intro j γ hγ
    have h0 : ψ (Additive.ofMul γ) = 0 := Subtype.ext (hφ γ hγ)
    rw [hc_apply, h0, map_zero, Finsupp.zero_apply]

  have hsum : φ = ∑ j, ((b j : S) : L) • castPost L (c j) := by
    refine AddMonoidHom.ext fun g => ?_
    rw [AddMonoidHom.finsetSum_apply]
    simp only [AddMonoidHom.smul_apply, castPost_apply, hc_apply, smul_eq_mul]
    have hx : ((ψ g : S) : L) = ∑ j, ((b.repr (ψ g) j : ℤ) : L) * ((b j : S) : L) := by
      conv_lhs => rw [← b.sum_repr (ψ g)]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, zsmul_eq_mul]
    rw [← hψ g, hx]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [hsum]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨⟨c j, (ModularCurve.Period.mem_parabolicHoms_iff).mpr (hc_par j)⟩, Set.mem_univ _, rfl⟩

theorem mem_span_range_castPost_basis {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    [Group.FG Γ] {L : Type*} [CommRing L] [NoZeroSMulDivisors ℤ L] {ι : Type*}
    (e : Module.Basis ι ℤ ↥(ModularCurve.Period.parabolicHoms ℤ Γ ℤ))
    (φ : Additive Γ →+ L) (hφ : φ ∈ ModularCurve.Period.parabolicHoms L Γ L) :
    φ ∈ Submodule.span L (Set.range fun i => castPost L (e i).1) := by
  classical
  refine (Submodule.span_le.mpr ?_) (mem_span_castPost_parabolicHoms φ hφ)
  rintro _ ⟨ψ, -, rfl⟩
  change castPost L ψ.1 ∈ Submodule.span L (Set.range fun i => castPost L (e i).1)

  have hψ : ψ.1 = ∑ i ∈ (e.repr ψ).support,
      (e.repr ψ i) • (e i : ↥(ModularCurve.Period.parabolicHoms ℤ Γ ℤ)).1 := by
    have h := congrArg Subtype.val (e.linearCombination_repr ψ).symm
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul]
  have hcast : castPost L ψ.1 = ∑ i ∈ (e.repr ψ).support,
      ((e.repr ψ i : ℤ) : L) • castPost L (e i : ↥(ModularCurve.Period.parabolicHoms ℤ Γ ℤ)).1 := by
    refine AddMonoidHom.ext fun g => ?_
    rw [castPost_apply, hψ, AddMonoidHom.finsetSum_apply, AddMonoidHom.finsetSum_apply, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, castPost_apply, zsmul_eq_mul, Int.cast_mul,
      Int.cast_id, smul_eq_mul]
  rw [hcast]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end ModularCurve.SpanCast
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SpanCast"
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsParabolicHom Period.parabolicHoms Period.mem_parabolicHoms_iff periodMap periodMap_injective periodMap_mem_parabolicHoms heckeOperatorHom_periodMap_of_isNormalizedEigenform heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd periodMap_add"
namespace SolC3c
p2m_open "ModularCurve"

open CongruenceSubgroup ModularCurve.Period HeckeEis

theorem postcomp_heckeOperatorHom (N ℓ : ℕ) [NeZero ℓ] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (g : A →+ B) (φ : Additive (Gamma0 N) →+ A) :
    g.comp (heckeOperatorHom N ℓ A φ) = heckeOperatorHom N ℓ B (g.comp φ) := by
  refine AddMonoidHom.ext fun γ => ?_
  obtain ⟨x, rfl⟩ : ∃ x : Gamma0 N, Additive.ofMul x = γ := ⟨γ.toMul, rfl⟩
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  show g (heckeOperatorHom N ℓ A φ (Additive.ofMul x))
    = heckeOperatorHom N ℓ B (g.comp φ) (Additive.ofMul x)
  rw [heckeOperatorHom_apply, heckeOperatorHom_apply, map_sum]
  rfl

theorem heckeOperatorHom_smul' (N ℓ : ℕ) [NeZero ℓ] {K : Type*} [CommRing K]
    (c : K) (φ : Additive (Gamma0 N) →+ K) :
    heckeOperatorHom N ℓ K (c • φ) = c • heckeOperatorHom N ℓ K φ := by
  refine AddMonoidHom.ext fun γ => ?_
  obtain ⟨x, rfl⟩ : ∃ x : Gamma0 N, Additive.ofMul x = γ := ⟨γ.toMul, rfl⟩
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  show heckeOperatorHom N ℓ K (c • φ) (Additive.ofMul x)
    = c • heckeOperatorHom N ℓ K φ (Additive.ofMul x)
  rw [heckeOperatorHom_apply, heckeOperatorHom_apply, Finset.smul_sum]
  rfl

variable {G : Type*} [Group G]

def intCastK (K : Type*) [AddCommGroupWithOne K] : (Additive G →+ ℤ) →+ (Additive G →+ K) :=
  AddMonoidHom.compHom (Int.castAddHom K)

@[scoped simp]
theorem intCastK_apply {K : Type*} [AddCommGroupWithOne K] (ψ : Additive G →+ ℤ)
    (x : Additive G) : intCastK K ψ x = (ψ x : K) := rfl

theorem isParabolicHom_intCastK {K : Type*} [AddCommGroupWithOne K]
    {Γ : Subgroup SL(2, ℤ)} {ψ : Additive Γ →+ ℤ}
    (hψ : IsParabolicHom Γ ψ) : IsParabolicHom Γ (intCastK K ψ) := by
  intro γ hγ
  simp only [intCastK_apply, hψ γ hγ, Int.cast_zero]

def parCast (K : Type*) [CommRing K] (Γ : Subgroup SL(2, ℤ)) (ψ : parabolicHoms ℤ Γ ℤ) :
    parabolicHoms K Γ K :=
  ⟨intCastK K (ψ : Additive Γ →+ ℤ), isParabolicHom_intCastK ψ.2⟩

@[scoped simp]
theorem parCast_coe {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)}
    (ψ : parabolicHoms ℤ Γ ℤ) :
    ((parCast K Γ ψ : parabolicHoms K Γ K) : Additive Γ →+ K)
      = intCastK K (ψ : Additive Γ →+ ℤ) := rfl

theorem intCastK_heckeOperatorHom (K : Type*) [AddCommGroupWithOne K] (N ℓ : ℕ) [NeZero ℓ]
    (ψ : Additive (Gamma0 N) →+ ℤ) :
    intCastK K (heckeOperatorHom N ℓ ℤ ψ) = heckeOperatorHom N ℓ K (intCastK K ψ) :=
  postcomp_heckeOperatorHom N ℓ (Int.castAddHom K) ψ

variable (N : ℕ) [NeZero N]

scoped instance : NoZeroSMulDivisors ℤ (Additive (Gamma0 N) →+ ℤ) := by
  constructor
  intro n φ h
  rcases eq_or_ne n 0 with rfl | hn
  · exact Or.inl rfl
  · refine Or.inr (AddMonoidHom.ext fun γ => ?_)
    have := DFunLike.congr_fun h γ
    simp only [AddMonoidHom.smul_apply, smul_eq_mul, AddMonoidHom.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left hn

scoped instance : NoZeroSMulDivisors ℤ (parabolicHoms ℤ (Gamma0 N) ℤ) := by
  constructor
  intro n ψ h
  rcases eq_or_ne n 0 with rfl | hn
  · exact Or.inl rfl
  · refine Or.inr (Subtype.ext (AddMonoidHom.ext fun γ => ?_))
    have := DFunLike.congr_fun (congrArg Subtype.val h) γ
    simp only [SetLike.val_smul, AddMonoidHom.smul_apply, smul_eq_mul,
      ZeroMemClass.coe_zero, AddMonoidHom.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left hn

scoped instance parabolicHoms_int_free : Module.Free ℤ (parabolicHoms ℤ (Gamma0 N) ℤ) :=
  Module.free_of_finite_type_torsion_free'

noncomputable abbrev b :
    Module.Basis (Fin (Module.finrank ℤ (parabolicHoms ℤ (Gamma0 N) ℤ))) ℤ
      (parabolicHoms ℤ (Gamma0 N) ℤ) :=
  Module.finBasis ℤ (parabolicHoms ℤ (Gamma0 N) ℤ)

local notation "rN" => Module.finrank ℤ (parabolicHoms ℤ (Gamma0 N) ℤ)

noncomputable def Tpar (ℓ : ℕ) [NeZero ℓ] : Module.End ℤ (parabolicHoms ℤ (Gamma0 N) ℤ) :=
  LinearMap.restrict (AddMonoidHom.toIntLinearMap (heckeOperatorHom N ℓ ℤ))
    (fun ψ hψ => heckeOperatorHom_preserves_parabolic N ℓ ℤ ψ hψ)

omit [NeZero N] in
theorem Tpar_coe (ℓ : ℕ) [NeZero ℓ] (ψ : parabolicHoms ℤ (Gamma0 N) ℤ) :
    ((Tpar N ℓ ψ : parabolicHoms ℤ (Gamma0 N) ℤ) : Additive (Gamma0 N) →+ ℤ)
      = heckeOperatorHom N ℓ ℤ (ψ : Additive (Gamma0 N) →+ ℤ) := rfl

noncomputable def Mℓ (ℓ : ℕ) [NeZero ℓ] : Matrix (Fin rN) (Fin rN) ℤ :=
  LinearMap.toMatrix (b N) (b N) (Tpar N ℓ)

variable {N}

omit [NeZero N] in

theorem parCast_add {K : Type*} [CommRing K] (ψ₁ ψ₂ : parabolicHoms ℤ (Gamma0 N) ℤ) :
    parCast K (Gamma0 N) (ψ₁ + ψ₂) = parCast K (Gamma0 N) ψ₁ + parCast K (Gamma0 N) ψ₂ :=
  Subtype.ext (map_add (intCastK K) _ _)

omit [NeZero N] in
theorem parCast_zsmul {K : Type*} [CommRing K] (n : ℤ) (ψ : parabolicHoms ℤ (Gamma0 N) ℤ) :
    parCast K (Gamma0 N) (n • ψ) = n • parCast K (Gamma0 N) ψ :=
  Subtype.ext (map_zsmul (intCastK K) _ _)

variable (N)

noncomputable def parCastLin (K : Type*) [CommRing K] :
    (Fin rN → K) →ₗ[K] parabolicHoms K (Gamma0 N) K :=
  (Finsupp.linearCombination K (fun i => parCast K (Gamma0 N) (b N i))).comp
    (Finsupp.linearEquivFunOnFinite K K (Fin rN)).symm.toLinearMap

theorem parCastLin_apply {K : Type*} [CommRing K] (c : Fin rN → K) :
    parCastLin N K c = ∑ i, c i • parCast K (Gamma0 N) (b N i) := by
  classical
  simp only [parCastLin, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype]
  · rfl
  · intro; exact zero_smul _ _

theorem range_parCastLin_eq_top :
    LinearMap.range (parCastLin N ℂ) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro φ -

  have h := ModularCurve.SpanCast.mem_span_range_castPost_basis (L := ℂ) (b N) φ.1 φ.2

  have hle : Submodule.span ℂ (Set.range fun i => ModularCurve.SpanCast.castPost ℂ (b N i).1)
      ≤ (LinearMap.range (parCastLin N ℂ)).map (parabolicHoms ℂ (Gamma0 N) ℂ).subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨parCast ℂ (Gamma0 N) (b N i), ⟨Pi.single i 1, ?_⟩, rfl⟩
    rw [parCastLin_apply, Finset.sum_eq_single i, Pi.single_eq_same, one_smul]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  obtain ⟨φ', hφ', hval⟩ := hle h
  rw [show φ = φ' from Subtype.ext hval.symm]
  exact hφ'

theorem periodMap_mem_range_parCastLin (f : CuspForm (Gamma0 N) 2) :
    (⟨ModularCurve.periodMap N f, ModularCurve.periodMap_mem_parabolicHoms ℂ f⟩ :
        parabolicHoms ℂ (Gamma0 N) ℂ) ∈ LinearMap.range (parCastLin N ℂ) := by
  rw [range_parCastLin_eq_top]; exact Submodule.mem_top

theorem heckeOperatorHom_parCastLin_eq {K : Type*} [CommRing K] (ℓ : ℕ) [NeZero ℓ]
    (c : Fin rN → K) :
    heckeOperatorHom N ℓ K ((parCastLin N K c : parabolicHoms K (Gamma0 N) K) :
        Additive (Gamma0 N) →+ K)
      = ((parCastLin N K (((Mℓ N ℓ).map (Int.castRingHom K)).mulVec c) :
          parabolicHoms K (Gamma0 N) K) : Additive (Gamma0 N) →+ K) := by
  classical
  have hcoe : ∀ (d : Fin rN → K),
      ((parCastLin N K d : parabolicHoms K (Gamma0 N) K) : Additive (Gamma0 N) →+ K)
        = ∑ i, d i • intCastK K ((b N i : parabolicHoms ℤ (Gamma0 N) ℤ) :
            Additive (Gamma0 N) →+ ℤ) := by
    intro d
    rw [parCastLin_apply, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [SetLike.val_smul, parCast_coe]
  rw [hcoe, hcoe, map_sum]
  have hterm : ∀ i, heckeOperatorHom N ℓ K (c i • intCastK K ((b N i :
      parabolicHoms ℤ (Gamma0 N) ℤ) : Additive (Gamma0 N) →+ ℤ))
      = c i • intCastK K (((Tpar N ℓ (b N i) : parabolicHoms ℤ (Gamma0 N) ℤ)) :
          Additive (Gamma0 N) →+ ℤ) := by
    intro i
    rw [heckeOperatorHom_smul', ← intCastK_heckeOperatorHom, ← Tpar_coe]
  simp only [hterm]
  have hTpar : ∀ i, Tpar N ℓ (b N i) = ∑ j, (Mℓ N ℓ) j i • b N j := by
    intro i
    conv_lhs => rw [← Module.Basis.sum_repr (b N) (Tpar N ℓ (b N i))]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Mℓ, LinearMap.toMatrix_apply]
  refine AddMonoidHom.ext fun γ => ?_
  simp only [hTpar, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, intCastK_apply,
    smul_eq_mul, Submodule.coe_sum, SetLike.val_smul, Matrix.mulVec, dotProduct,
    Matrix.map_apply, Int.coe_castRingHom, Int.cast_sum, Int.cast_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem parCastLin_injective {K : Type*} [Field K] :
    Function.Injective (parCastLin N K) := by
  classical

  suffices hLI : LinearIndependent K (fun i => intCastK K ((b N i).1 : Additive (Gamma0 N) →+ ℤ)) by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hc' : ((parCastLin N K c : parabolicHoms K (Gamma0 N) K) :
        Additive (Gamma0 N) →+ K) = 0 := by rw [hc]; rfl
    rw [parCastLin_apply, Submodule.coe_sum] at hc'
    simp only [SetLike.val_smul, parCast_coe] at hc'
    exact linearIndependent_iff'.mp hLI Finset.univ c (by rw [hc'])
      |> fun h => funext fun i => h i (Finset.mem_univ i)

  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (instGroupFG_Gamma0 N)
  haveI : Fintype S := hSfin.fintype

  let evK : (Additive (Gamma0 N) →+ K) →ₗ[K] (S → K) :=
    { toFun := fun ψ s => ψ (Additive.ofMul (s : Gamma0 N))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

  refine LinearIndependent.of_comp evK ?_

  show LinearIndependent K (fun i s => (((evalGen (G := Gamma0 N) S) (b N i).1 s : ℤ) : K))

  let P : Submodule ℤ (S → ℤ) :=
    LinearMap.range ((evalGen (G := Gamma0 N) S).comp (parabolicHoms ℤ (Gamma0 N) ℤ).subtype)

  have hPsat : ∀ (n : ℤ) (_ : n ≠ 0) (v : S → ℤ), n • v ∈ P → v ∈ P := by
    intro n hn v ⟨ψ, hψ⟩

    have hdiv : ∀ γ : Gamma0 N, n ∣ ψ.1 (Additive.ofMul γ) := by
      intro γ
      have hmem : γ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top _
      induction hmem using Subgroup.closure_induction with
      | mem s hs =>
          refine ⟨v ⟨s, hs⟩, ?_⟩
          have := congrFun hψ ⟨s, hs⟩
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, Pi.smul_apply,
            smul_eq_mul] at this
          exact this
      | one => exact ⟨0, by simp⟩
      | mul x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
          refine ⟨a + b, ?_⟩
          show ψ.1 (Additive.ofMul x + Additive.ofMul y) = n * (a + b)
          rw [map_add, ha, hb]; ring
      | inv x _ hx =>
          obtain ⟨a, ha⟩ := hx
          refine ⟨-a, ?_⟩
          show ψ.1 (- Additive.ofMul x) = n * (-a)
          rw [map_neg, ha]; ring

    refine ⟨⟨{ toFun := fun γ => ψ.1 γ / n,
                map_zero' := by simp,
                map_add' := fun a b => by
                  rw [map_add,
                    Int.add_ediv_of_dvd_left (by simpa using hdiv (Additive.toMul a))] }, ?_⟩, ?_⟩
    ·
      intro γ hγ; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, ψ.2 γ hγ, Int.zero_ediv]
    ·
      funext s
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, evalGen, LinearMap.coe_mk,
        AddHom.coe_mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      have hs := congrFun hψ s
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, Pi.smul_apply, smul_eq_mul,
        evalGen, LinearMap.coe_mk, AddHom.coe_mk] at hs
      rw [hs, Int.mul_ediv_cancel_left _ hn]

  obtain ⟨n', snf⟩ := P.smithNormalForm (Pi.basisFun ℤ S)

  have ha_unit : ∀ i, IsUnit (snf.a i) := by
    intro i
    have hne : snf.a i ≠ 0 := by
      intro h
      have := snf.snf i; rw [h, zero_smul] at this
      exact (snf.bN).ne_zero i (Subtype.ext this)
    have hmem : snf.a i • snf.bM (snf.f i) ∈ P := (snf.snf i) ▸ (snf.bN i).2
    have hbMmem : snf.bM (snf.f i) ∈ P := hPsat (snf.a i) hne _ hmem

    have heq : snf.bN i = snf.a i • (⟨snf.bM (snf.f i), hbMmem⟩ : P) :=
      Subtype.ext (snf.snf i)
    have := congrArg (fun x => (snf.bN).repr x i) heq
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply,
      smul_eq_mul] at this
    exact .of_mul_eq_one _ this.symm

  let einj : parabolicHoms ℤ (Gamma0 N) ℤ ≃ₗ[ℤ] P :=
    LinearEquiv.ofInjective
      ((evalGen (G := Gamma0 N) S).comp (parabolicHoms ℤ (Gamma0 N) ℤ).subtype)
      ((evalGen_injective hS).comp Subtype.val_injective)
  let bP : Module.Basis (Fin rN) ℤ P := (b N).map einj
  have hbP_coe : ∀ i, ((bP i : P) : S → ℤ) = evalGen (G := Gamma0 N) S (b N i).1 := fun i => rfl

  let eidx : Fin n' ≃ Fin rN := snf.bN.indexEquiv bP
  let bP' : Module.Basis (Fin n') ℤ P := bP.reindex eidx.symm

  have hW_unit : IsUnit (snf.bN.toMatrix bP').det := by
    have h := Module.Basis.toMatrix_mul_toMatrix_flip snf.bN bP'
    have hdet : (snf.bN.toMatrix bP').det * (bP'.toMatrix snf.bN).det = 1 := by
      rw [← Matrix.det_mul, h, Matrix.det_one]
    exact .of_mul_eq_one _ hdet

  rw [Fintype.linearIndependent_iff]
  intro g hg i

  have hrepr : ∀ (l : Fin n') (i' : Fin rN),
      snf.bM.repr ((bP i' : P) : S → ℤ) (snf.f l)
        = snf.a l * (snf.bN.toMatrix bP') l (eidx.symm i') := by
    intro l i'
    have hbP : bP i' = bP' (eidx.symm i') := by
      simp only [bP', Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    rw [hbP]
    have := snf.repr_apply_embedding_eq_repr_smul (m := bP' (eidx.symm i')) (i := l)
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.toMatrix_apply]

  have hrepr_sum : ∀ (l : Fin n') (v : S → ℤ),
      snf.bM.repr v (snf.f l) = ∑ s, (snf.bM.repr (Pi.single s 1) (snf.f l)) * v s := by
    intro l v
    have hv : v = ∑ s, v s • (Pi.single s 1 : S → ℤ) := by
      funext s'; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv, map_sum]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, mul_comm]

  have hΛ : ∀ l : Fin n',
      ∑ i', g i' * ((snf.bM.repr ((bP i' : P) : S → ℤ) (snf.f l) : ℤ) : K) = 0 := by
    intro l
    calc ∑ i', g i' * ((snf.bM.repr ((bP i' : P) : S → ℤ) (snf.f l) : ℤ) : K)
        = ∑ i', g i' * ∑ s, ((snf.bM.repr (Pi.single s 1) (snf.f l) : ℤ) : K)
            * (((evalGen (G := Gamma0 N) S (b N i').1) s : ℤ) : K) := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          congr 1
          rw [hrepr_sum l, Int.cast_sum, ← hbP_coe i']
          refine Finset.sum_congr rfl fun s _ => ?_
          push_cast; ring
      _ = ∑ s, ((snf.bM.repr (Pi.single s 1) (snf.f l) : ℤ) : K)
            * ∑ i', g i' * (((evalGen (G := Gamma0 N) S (b N i').1) s : ℤ) : K) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i' _ => ?_; ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun s _ => ?_
          have := congrFun hg s
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
          rw [this, mul_zero]

  have hWg : ∀ l : Fin n',
      ∑ i', ((snf.bN.toMatrix bP') l (eidx.symm i') : K) * g i' = 0 := by
    intro l
    have h := hΛ l
    simp only [hrepr, Int.cast_mul, ← mul_assoc] at h
    have ha_ne : ((snf.a l : ℤ) : K) ≠ 0 := by
      rcases Int.isUnit_iff.mp (ha_unit l) with h1 | h1 <;> simp [h1]
    have h2 : ((snf.a l : ℤ) : K) * ∑ i', g i' * ((snf.bN.toMatrix bP') l (eidx.symm i') : K) = 0 := by
      rw [Finset.mul_sum]; convert h using 1
      refine Finset.sum_congr rfl fun i' _ => ?_; ring
    rw [mul_eq_zero] at h2
    have h3 := h2.resolve_left ha_ne
    rw [← h3]; refine Finset.sum_congr rfl fun i' _ => ?_; ring

  have hWg' :
      ((snf.bN.toMatrix bP').map (Int.castRingHom K)).mulVec (g ∘ eidx) = 0 := by
    funext l
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← Equiv.sum_comp eidx.symm (fun i' =>
      ((snf.bN.toMatrix bP').map (Int.castRingHom K)) l i' * (g ∘ eidx) i')]
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Matrix.map_apply,
      Int.coe_castRingHom]
    exact hWg l

  have hWK_det_ne : (((snf.bN.toMatrix bP').map (Int.castRingHom K)).det) ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rcases Int.isUnit_iff.mp hW_unit with h1 | h1 <;> simp [h1]
  have hgz : g ∘ eidx = 0 := by
    by_contra hne
    exact hWK_det_ne (Matrix.exists_mulVec_eq_zero_iff.mp ⟨g ∘ eidx, hne, hWg'⟩)

  have := congrFun hgz (eidx.symm i)
  simpa using this

end ModularCurve.SolC3c
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SpanCast P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SolC3c"
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SpanCast"

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsParabolicHom Period.parabolicHoms Period.mem_parabolicHoms_iff periodMap periodMap_injective periodMap_mem_parabolicHoms heckeOperatorHom_periodMap_of_isNormalizedEigenform heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd periodMap_add"
namespace MinorsKernel
p2m_open "ModularCurve"

theorem det_submatrix_eq_zero_of_mulVec_eq_zero {A : Type*} [CommRing A] [IsDomain A]
    {m r : ℕ} (S : Matrix (Fin m) (Fin r) A) {v : Fin r → A} (hv : v ≠ 0)
    (hSv : S.mulVec v = 0) (e : Fin r ↪ Fin m) :
    (S.submatrix e id).det = 0 := by
  classical
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  ext i
  have := congrFun hSv (e i)
  simpa [Matrix.mulVec, Matrix.submatrix] using this

theorem exists_mulVec_eq_zero_of_forall_det_submatrix_eq_zero {K : Type*} [Field K]
    {m r : ℕ} (S : Matrix (Fin m) (Fin r) K)
    (h : ∀ e : Fin r ↪ Fin m, (S.submatrix e id).det = 0) :
    ∃ v : Fin r → K, v ≠ 0 ∧ S.mulVec v = 0 := by
  classical
  by_contra hno
  push Not at hno
  have hinj : Function.Injective S.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    exact hno v hv0 (by simpa using hv)
  have hrank : S.rank = r := by
    unfold Matrix.rank
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have hrow : Module.finrank K (Submodule.span K (Set.range S.row)) = r := by
    rw [← Matrix.rank_eq_finrank_span_row]; exact hrank
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (K := K) S.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    have h1 := finrank_span_eq_card (R := K) hli
    rw [hspan, hrow] at h1
    exact h1.symm
  let e0 : κ ≃ Fin r := Fintype.equivFinOfCardEq hcard
  let e : Fin r ↪ Fin m := ⟨a ∘ e0.symm, ha.comp e0.symm.injective⟩
  have hrows : LinearIndependent K (S.submatrix e id).row := by
    have : (S.submatrix e id).row = S.row ∘ a ∘ e0.symm := by
      funext i; rfl
    rw [this]
    exact hli.comp _ e0.symm.injective
  have hunit : IsUnit (S.submatrix e id) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
  exact hunit (h e)

theorem exists_mulVec_eq_zero_iff_forall_det_submatrix_eq_zero {K : Type*} [Field K]
    {m r : ℕ} (S : Matrix (Fin m) (Fin r) K) :
    (∃ v : Fin r → K, v ≠ 0 ∧ S.mulVec v = 0) ↔ ∀ e : Fin r ↪ Fin m, (S.submatrix e id).det = 0 :=
  ⟨fun ⟨_, hv, hSv⟩ e => det_submatrix_eq_zero_of_mulVec_eq_zero S hv hSv e,
    exists_mulVec_eq_zero_of_forall_det_submatrix_eq_zero S⟩

theorem map_det_submatrix {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {m r : ℕ} (S : Matrix (Fin m) (Fin r) A) (e : Fin r ↪ Fin m) :
    φ (S.submatrix e id).det = ((S.map φ).submatrix e id).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

theorem det_submatrix_eq_zero_iff_of_injective {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ)
    {m r : ℕ} (S : Matrix (Fin m) (Fin r) A) (e : Fin r ↪ Fin m) :
    (S.submatrix e id).det = 0 ↔ ((S.map φ).submatrix e id).det = 0 := by
  rw [← map_det_submatrix, ← map_zero φ]
  exact ⟨fun h => by rw [h], fun h => hφ h⟩

theorem exists_mulVec_eq_zero_map_of_map_injective {A L k : Type*} [CommRing A] [Field L]
    [Field k] (ι : A →+* L) (hι : Function.Injective ι) (red : A →+* k)
    {m r : ℕ} (S : Matrix (Fin m) (Fin r) A)
    (hL : ∃ v : Fin r → L, v ≠ 0 ∧ (S.map ι).mulVec v = 0) :
    ∃ w : Fin r → k, w ≠ 0 ∧ (S.map red).mulVec w = 0 := by
  rw [exists_mulVec_eq_zero_iff_forall_det_submatrix_eq_zero] at hL ⊢
  intro e
  have h0 : (S.submatrix e id).det = 0 := (det_submatrix_eq_zero_iff_of_injective ι hι S e).mpr (hL e)
  rw [← map_det_submatrix, h0, map_zero]

theorem exists_mulVec_eq_zero_map_of_map_injective' {A L k : Type*} [CommRing A] [Field L]
    [Field k] (ι : A →+* L) (hι : Function.Injective ι) (red : A →+* k)
    {ρ : Type*} [Fintype ρ] {r : ℕ} (S : Matrix ρ (Fin r) A)
    (hL : ∃ v : Fin r → L, v ≠ 0 ∧ (S.map ι).mulVec v = 0) :
    ∃ w : Fin r → k, w ≠ 0 ∧ (S.map red).mulVec w = 0 := by
  classical
  let e := Fintype.equivFin ρ
  have h := exists_mulVec_eq_zero_map_of_map_injective ι hι red
    (S.submatrix e.symm id) (by
      obtain ⟨v, hv, hSv⟩ := hL
      refine ⟨v, hv, ?_⟩
      ext i
      have := congrFun hSv (e.symm i)
      simpa [Matrix.mulVec, Matrix.submatrix, Matrix.map] using this)
  obtain ⟨w, hw, hSw⟩ := h
  refine ⟨w, hw, ?_⟩
  ext i
  have := congrFun hSw (e i)
  simpa [Matrix.mulVec, Matrix.submatrix, Matrix.map] using this

end ModularCurve.MinorsKernel
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SpanCast P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SolC3c"
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SpanCast P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SolC3c"

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsParabolicHom Period.parabolicHoms Period.mem_parabolicHoms_iff periodMap periodMap_injective periodMap_mem_parabolicHoms heckeOperatorHom_periodMap_of_isNormalizedEigenform heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd periodMap_add"
namespace SolC3c
p2m_open "ModularCurve"

open CongruenceSubgroup ModularCurve.Period HeckeEis

variable (N : ℕ) [NeZero N]

local notation "rN" => Module.finrank ℤ (parabolicHoms ℤ (Gamma0 N) ℤ)

end ModularCurve.SolC3c
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SpanCast P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SolC3c"
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SpanCast P2MW.S_ModularCurve_Period_exists_parabolicRealization.ModularCurve.SolC3c"

open CongruenceSubgroup ModularCurve.Period HeckeEis ModularCurve.SolC3c ModularCurve.MinorsKernel in
theorem solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (hint : f.PrimeCoeffsIntegral)
    (k : Type) [Field k] (red : integralClosure ℤ ℂ →+* k) :
    ∃ f₀ : ModularCurve.Period.parabolicHoms k (Gamma0 N) k, f₀ ≠ 0 ∧
      ∀ (ℓ : ℕ) (_ : NeZero ℓ) (hℓp : ℓ.Prime),
        HeckeEis.heckeOperatorHom N ℓ k (f₀ : Additive (Gamma0 N) →+ k) =
          (red (CuspForm.eigenLift hint ⟨ℓ, hℓp⟩)) •
            (f₀ : Additive (Gamma0 N) →+ k) := by
  classical
  set rN := Module.finrank ℤ (parabolicHoms ℤ (Gamma0 N) ℤ)

  have hpm_mem : (⟨ModularCurve.periodMap N f, ModularCurve.periodMap_mem_parabolicHoms ℂ f⟩ :
      parabolicHoms ℂ (Gamma0 N) ℂ) ∈ LinearMap.range (parCastLin N ℂ) :=
    periodMap_mem_range_parCastLin N f
  obtain ⟨c, hc⟩ := hpm_mem

  have hf_ne : f ≠ 0 := by
    intro hf0
    have h1 := hf.qCoeff_one
    rw [hf0] at h1

    have hcf : UpperHalfPlane.cuspFunction 1 ((0 : CuspForm (Gamma0 N) 2) : UpperHalfPlane → ℂ)
        = 0 := by
      rw [CuspForm.coe_zero]
      funext q
      rcases eq_or_ne q 0 with rfl | hq
      · exact Function.Periodic.cuspFunction_zero_of_zero_at_inf one_pos tendsto_const_nhds
      · simp only [UpperHalfPlane.cuspFunction,
          Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq, Function.comp_apply, Pi.zero_apply]
    have h0 : ModularFormClass.qCoeff ((0 : CuspForm (Gamma0 N) 2) : UpperHalfPlane → ℂ) 1 = 0 := by
      simp only [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_coeff, hcf]
      have : iteratedDeriv 1 (0 : ℂ → ℂ) = 0 := by
        funext x
        have h0' : (0 : ℂ → ℂ) = fun _ => (0 : ℂ) := rfl
        rw [h0', iteratedDeriv_const]; simp
      rw [this]; simp
    rw [h0] at h1
    exact one_ne_zero h1.symm

  have hpm_zero : ModularCurve.periodMap N (0 : CuspForm (Gamma0 N) 2) = 0 := by
    have h := ModularCurve.periodMap_add (N := N) 0 0
    rw [add_zero] at h
    have h2 : ModularCurve.periodMap N 0 + ModularCurve.periodMap N 0
        = ModularCurve.periodMap N 0 + 0 := by rw [← h, add_zero]
    exact add_left_cancel h2
  have hpm_ne : ModularCurve.periodMap N f ≠ 0 := by
    intro h
    exact hf_ne (ModularCurve.periodMap_injective (h.trans hpm_zero.symm))
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply hpm_ne
    have : parCastLin N ℂ c = 0 := by rw [hc0]; exact map_zero _
    rw [hc] at this
    exact congrArg Subtype.val this

  have hEig : ∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      ((Mℓ N ℓ).map (Int.castRingHom ℂ) - (ModularFormClass.qCoeff f (ℓ : ℕ)) • 1).mulVec c = 0 := by
    intro ℓ
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩

    have heig : HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f)
        = (ModularFormClass.qCoeff f (ℓ : ℕ)) • ModularCurve.periodMap N f := by
      by_cases hdvd : (ℓ : ℕ) ∣ N
      · exact ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd hf
          ℓ.2 hdvd
      · exact ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform hf ℓ.2 hdvd
    have hc' : ((parCastLin N ℂ c : parabolicHoms ℂ (Gamma0 N) ℂ) :
        Additive (Gamma0 N) →+ ℂ) = ModularCurve.periodMap N f := congrArg Subtype.val hc
    have hsub : parCastLin N ℂ (((Mℓ N ℓ).map (Int.castRingHom ℂ)).mulVec c)
        = parCastLin N ℂ ((ModularFormClass.qCoeff f (ℓ : ℕ)) • c) := by
      apply Subtype.ext
      rw [← heckeOperatorHom_parCastLin_eq, map_smul, SetLike.val_smul, hc', heig]
    have hvec := parCastLin_injective N hsub
    rw [Matrix.sub_mulVec, hvec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact sub_self _

  let Kℓ : Nat.Primes → Submodule k (Fin rN → k) := fun ℓ =>
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    LinearMap.ker
      (Matrix.mulVecLin ((Mℓ N ℓ).map (Int.castRingHom k) - (red (CuspForm.eigenLift hint ℓ)) • 1))
  let KF : Finset Nat.Primes → Submodule k (Fin rN → k) := fun F => ⨅ ℓ ∈ F, Kℓ ℓ

  have hKF_ne : ∀ F : Finset Nat.Primes, KF F ≠ ⊥ := by
    intro F

    let ι : integralClosure ℤ ℂ →+* ℂ := (integralClosure ℤ ℂ).subtype
    have hι_inj : Function.Injective ι := Subtype.val_injective

    have hι_int : (ι.comp (algebraMap ℤ (integralClosure ℤ ℂ))) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    have hred_int : (red.comp (algebraMap ℤ (integralClosure ℤ ℂ))) = Int.castRingHom k :=
      RingHom.ext_int _ _
    let block : Nat.Primes → Matrix (Fin rN) (Fin rN) (integralClosure ℤ ℂ) := fun ℓ =>
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      (Mℓ N ℓ).map (algebraMap ℤ (integralClosure ℤ ℂ)) - (CuspForm.eigenLift hint ℓ) • 1
    let S : Matrix (F × Fin rN) (Fin rN) (integralClosure ℤ ℂ) :=
      fun p j => block p.1.1 p.2 j

    have hSc : (S.map ι).mulVec c = 0 := by
      funext p
      obtain ⟨⟨ℓ, hℓF⟩, i⟩ := p
      have hblock : (block ℓ).map ι
          = haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
            (Mℓ N ℓ).map (Int.castRingHom ℂ) - (ModularFormClass.qCoeff f (ℓ : ℕ)) • 1 := by
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        ext a b'
        simp only [block, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, map_sub]
        congr 1
        simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, apply_ite ι, map_zero]
        congr 1
        exact CuspForm.eigenLift_coe hint ℓ
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      have hrow : (S.map ι).mulVec c (⟨ℓ, hℓF⟩, i) = ((block ℓ).map ι).mulVec c i := by
        simp only [Matrix.mulVec, S, Matrix.map_apply, dotProduct]
      rw [hrow, hblock]
      exact congrFun (hEig ℓ) i

    obtain ⟨w, hw_ne, hSw⟩ :=
      exists_mulVec_eq_zero_map_of_map_injective' ι hι_inj red S ⟨c, hc_ne, hSc⟩

    have hw_KF : w ∈ KF F := by
      simp only [KF, Submodule.mem_iInf]
      intro ℓ hℓF
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      simp only [Kℓ, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hblock_red : (block ℓ).map red
          = (Mℓ N ℓ).map (Int.castRingHom k) - (red (CuspForm.eigenLift hint ℓ)) • 1 := by
        ext a b'
        simp only [block, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, map_sub]
        congr 1
        · exact congrFun (congrArg DFunLike.coe hred_int) (Mℓ N ℓ a b')
        · simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, apply_ite red, map_zero]
      funext i
      have hrow : (S.map red).mulVec w (⟨ℓ, hℓF⟩, i) = ((block ℓ).map red).mulVec w i := by
        simp only [Matrix.mulVec, S, Matrix.map_apply, dotProduct]
      have := congrFun hSw (⟨ℓ, hℓF⟩, i)
      rw [hrow, hblock_red] at this
      exact this
    exact fun hbot => hw_ne (by rw [hbot] at hw_KF; exact hw_KF)

  have hStab : ∃ F₀ : Finset Nat.Primes, ∀ ℓ : Nat.Primes, KF F₀ ≤ Kℓ ℓ := by
    have hex : ∃ n, ∃ F : Finset Nat.Primes, Module.finrank k (KF F) = n := ⟨_, ∅, rfl⟩
    obtain ⟨F₀, hF₀d⟩ : ∃ F, Module.finrank k (KF F) = Nat.find hex := Nat.find_spec hex
    refine ⟨F₀, fun ℓ => ?_⟩
    have hle : KF (insert ℓ F₀) ≤ KF F₀ := by
      simp only [KF, Finset.iInf_insert]
      exact inf_le_right
    have hfr : Module.finrank k (KF F₀) ≤ Module.finrank k (KF (insert ℓ F₀)) := by
      rw [hF₀d]; exact Nat.find_min' hex ⟨_, rfl⟩
    have heq : KF (insert ℓ F₀) = KF F₀ := Submodule.eq_of_le_of_finrank_le hle hfr
    calc KF F₀ = KF (insert ℓ F₀) := heq.symm
      _ ≤ Kℓ ℓ := by simp only [KF, Finset.iInf_insert]; exact inf_le_left
  obtain ⟨F₀, hF₀⟩ := hStab

  obtain ⟨w, hwF₀, hw_ne⟩ : ∃ w, w ∈ KF F₀ ∧ w ≠ 0 := by
    rcases Submodule.exists_mem_ne_zero_of_ne_bot (hKF_ne F₀) with ⟨w, hw1, hw2⟩
    exact ⟨w, hw1, hw2⟩

  refine ⟨parCastLin N k w, ?_, ?_⟩
  ·
    intro hf0
    exact hw_ne (parCastLin_injective N (by rw [hf0]; exact (map_zero _).symm))
  ·
    intro ℓ hℓ hℓp
    have hwKℓ : w ∈ Kℓ ⟨ℓ, hℓp⟩ := hF₀ ⟨ℓ, hℓp⟩ hwF₀

    have hMw : ((Mℓ N ℓ).map (Int.castRingHom k)).mulVec w
        = (red (CuspForm.eigenLift hint ⟨ℓ, hℓp⟩)) • w := by
      have hker := (LinearMap.mem_ker).mp hwKℓ
      simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec] at hker
      rw [sub_eq_zero] at hker
      rw [hker, Matrix.smul_mulVec, Matrix.one_mulVec]

    rw [heckeOperatorHom_parCastLin_eq N ℓ w, hMw, map_smul]
    rfl

#print axioms solution

end S_ModularCurve_Period_exists_parabolicRealization
end P2MW
export P2MW.S_ModularCurve_Period_exists_parabolicRealization (solution)
