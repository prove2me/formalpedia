-- Prove2me | solution 1 for ModularCurve.exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4ae97585-46c7-5220-b8b5-eeccae7be9db

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd

set_option autoImplicit false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

namespace KummerRowPackaging

variable {R : Type} [CommRing R] (S : Submonoid R)
  {A B A' B' : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
  [Module R A] [Module R B] [Module R A'] [Module R B']
  (fA : A →ₗ[R] A') [IsLocalizedModule S fA] (fB : B →ₗ[R] B') [IsLocalizedModule S fB]

theorem map_smul_id (c : R) :
    IsLocalizedModule.map S fA fA (c • (LinearMap.id : A →ₗ[R] A)) = c • LinearMap.id := by
  rw [LinearMap.map_smul, IsLocalizedModule.map_id]

theorem ker_map_eq_range_smul_id (δ : A →ₗ[R] B) (c : R)
    (h : LinearMap.ker δ = LinearMap.range (c • (LinearMap.id : A →ₗ[R] A))) :
    LinearMap.ker (IsLocalizedModule.map S fA fB δ)
      = LinearMap.range (c • (LinearMap.id : A' →ₗ[R] A')) := by
  have hex : Function.Exact (c • (LinearMap.id : A →ₗ[R] A)) δ :=
    LinearMap.exact_iff.mpr h
  have hex' := IsLocalizedModule.map_exact S fA fA fB _ _ hex
  rw [map_smul_id] at hex'
  exact LinearMap.exact_iff.mp hex'

end KummerRowPackaging

namespace KummerRowPackaging

theorem localized_smul_eq_zero {R : Type} [CommRing R] (S : Submonoid R) {B B' : Type}
    [AddCommGroup B] [AddCommGroup B'] [Module R B] [Module R B']
    (fB : B →ₗ[R] B') [IsLocalizedModule S fB]
    (c : R) (hB : ∀ x : B, c • x = 0) (y : B') : c • y = 0 := by
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S fB y
  rw [Function.uncurry_apply_pair, ← IsLocalizedModule.mk'_smul, hB, IsLocalizedModule.mk'_zero]

end KummerRowPackaging

open KummerRowPackaging in
theorem perLevel
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (m : ℕ)
    (𝒥m : Sheaf (smallFppfTopology specInt) Ab.{1})
    (M0int H1K M0loc H1Kloc : Type)
    [AddCommGroup M0int] [AddCommGroup H1K] [AddCommGroup M0loc] [AddCommGroup H1Kloc]
    [Module HeckeAlg M0int] [Module HeckeAlg H1K] [Module HeckeAlg M0loc] [Module HeckeAlg H1Kloc]
    (δ : M0int →ₗ[HeckeAlg] H1K)
    (hδ : LinearMap.ker δ = LinearMap.range ((q ^ m : HeckeAlg) • (LinearMap.id : M0int →ₗ[HeckeAlg] M0int)))
    (hH1K : ∀ x : H1K, (q ^ m : HeckeAlg) • x = 0)
    (ℓ0 : M0int →ₗ[HeckeAlg] M0loc) [IsLocalizedModule (eisensteinMaximalIdeal p q).primeCompl ℓ0]
    (ℓ1 : H1K →ₗ[HeckeAlg] H1Kloc) [IsLocalizedModule (eisensteinMaximalIdeal p q).primeCompl ℓ1]
    (eH1 : H1Kloc ≃+ fppfCohomology specInt 𝒥m 1)
    (M : Type) [AddCommGroup M] (toM : M0loc →+ M)
    (htoM : Function.Injective toM) (hfin : toM.range.FiniteIndex) :
    ∃ row : JKummerRow q m M,
      Nonempty (letI := row.instH1Jtors; row.H1Jtors ≃+ fppfCohomology specInt 𝒥m 1) := by
  set S := (eisensteinMaximalIdeal p q).primeCompl with hS

  let δloc : M0loc →ₗ[HeckeAlg] H1Kloc := IsLocalizedModule.map S ℓ0 ℓ1 δ
  have hker : LinearMap.ker δloc
      = LinearMap.range ((q ^ m : HeckeAlg) • (LinearMap.id : M0loc →ₗ[HeckeAlg] M0loc)) :=
    ker_map_eq_range_smul_id S ℓ0 ℓ1 δ _ hδ
  have hkill : ∀ y : H1Kloc, (q ^ m : HeckeAlg) • y = 0 :=
    localized_smul_eq_zero S ℓ1 _ hH1K

  have hqT : ((q : HeckeAlg) ^ m) = (((q : ℤ) ^ m : ℤ) : HeckeAlg) := by push_cast; rfl
  have hsc0 : ∀ x : M0loc, (q ^ m : HeckeAlg) • x = ((q : ℤ) ^ m) • x := fun x => by
    rw [hqT, Int.cast_smul_eq_zsmul]
  have hsc1 : ∀ x : H1Kloc, (q ^ m : HeckeAlg) • x = ((q : ℤ) ^ m) • x := fun x => by
    rw [hqT, Int.cast_smul_eq_zsmul]
  refine ⟨{ M0 := M0loc
            H1Jtors := H1Kloc
            H1J := H1Kloc ⧸ LinearMap.range δloc
            toM := toM
            toM_injective := htoM
            toM_finiteIndex := hfin
            delta := δloc.toAddMonoidHom
            push := (LinearMap.range δloc).mkQ.toAddMonoidHom
            delta_ker := ?_
            exact_delta_push := ?_
            push_range := ?_ }, ⟨eH1⟩⟩
  ·
    ext x
    constructor
    · intro hx
      have hx' : x ∈ LinearMap.ker δloc := hx
      rw [hker] at hx'
      obtain ⟨y, rfl⟩ := hx'
      refine ⟨y, ?_⟩
      show ((q : ℤ) ^ m) • y = ((q ^ m : HeckeAlg) • (LinearMap.id : M0loc →ₗ[HeckeAlg] M0loc)) y
      rw [LinearMap.smul_apply, LinearMap.id_apply, hsc0]
    · rintro ⟨y, rfl⟩
      show ((q : ℤ) ^ m • AddMonoidHom.id M0loc) y ∈ LinearMap.ker δloc
      rw [hker]
      refine ⟨y, ?_⟩
      show ((q ^ m : HeckeAlg) • (LinearMap.id : M0loc →ₗ[HeckeAlg] M0loc)) y = ((q : ℤ) ^ m) • y
      rw [LinearMap.smul_apply, LinearMap.id_apply, hsc0]
  · exact LinearMap.exact_map_mkQ_range δloc
  ·
    rw [AddMonoidHom.range_eq_top.mpr (Submodule.mkQ_surjective _), eq_comm, eq_top_iff]
    rintro z -
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range δloc) z
    show ((q : ℤ) ^ m) • (LinearMap.range δloc).mkQ y = 0
    rw [← map_zsmul, ← hsc1, hkill, map_zero]

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (hqn : q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12)
    (𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
    (M0int H1K M0loc H1Kloc : ℕ → Type)
    [∀ m, AddCommGroup (M0int m)] [∀ m, AddCommGroup (H1K m)]
    [∀ m, AddCommGroup (M0loc m)] [∀ m, AddCommGroup (H1Kloc m)]
    [∀ m, Module HeckeAlg (M0int m)] [∀ m, Module HeckeAlg (H1K m)]
    [∀ m, Module HeckeAlg (M0loc m)] [∀ m, Module HeckeAlg (H1Kloc m)]
    (δ : ∀ m, M0int m →ₗ[HeckeAlg] H1K m)
    (hδ : ∀ m, LinearMap.ker (δ m)
      = LinearMap.range ((q ^ m : HeckeAlg) • (LinearMap.id : M0int m →ₗ[HeckeAlg] M0int m)))
    (hH1K : ∀ m, ∀ x : H1K m, (q ^ m : HeckeAlg) • x = 0)
    (ℓ0 : ∀ m, M0int m →ₗ[HeckeAlg] M0loc m)
    [∀ m, IsLocalizedModule (eisensteinMaximalIdeal p q).primeCompl (ℓ0 m)]
    (ℓ1 : ∀ m, H1K m →ₗ[HeckeAlg] H1Kloc m)
    [∀ m, IsLocalizedModule (eisensteinMaximalIdeal p q).primeCompl (ℓ1 m)]
    (eH1 : ∀ m, H1Kloc m ≃+ fppfCohomology specInt (𝒥 m) 1)
    (M : Type) [AddCommGroup M] (toM : ∀ m, M0loc m →+ M)
    (htoM : ∀ m, Function.Injective (toM m)) (hfin : ∀ m, (toM m).range.FiniteIndex) :
    ∃ row : ∀ m, JKummerRow q m M,
      ∀ m, Nonempty (letI := (row m).instH1Jtors; (row m).H1Jtors ≃+ fppfCohomology specInt (𝒥 m) 1) := by
  have h := fun m => perLevel p q m (𝒥 m) (M0int m) (H1K m) (M0loc m) (H1Kloc m) (δ m) (hδ m) (hH1K m)
    (ℓ0 m) (ℓ1 m) (eH1 m) M (toM m) (htoM m) (hfin m)
  choose row hrow using h
  exact ⟨row, hrow⟩

end S_ModularCurve_exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd
end P2MW
export P2MW.S_ModularCurve_exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd (solution)
