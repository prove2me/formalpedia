-- Prove2me | solution 1 for Module.length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bcc7bc49-9b54-593c-8cdb-34d11e773d6e

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Module.Projective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq

set_option autoImplicit false

universe u v w x

namespace M4cP4PairB

open Module Submodule Pointwise

section PID

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪]

theorem length_quotient_smul_top (F : Type*) [AddCommGroup F] [Module 𝒪 F] [Module.Free 𝒪 F]
    [Module.Finite 𝒪 F] (c : 𝒪) :
    Module.length 𝒪 (F ⧸ (c • (⊤ : Submodule 𝒪 F))) =
      (Module.finrank 𝒪 F : ℕ∞) * Module.length 𝒪 (𝒪 ⧸ Ideal.span ({c} : Set 𝒪)) := by
  classical
  set n := Module.finrank 𝒪 F
  let b := Module.finBasis 𝒪 F
  let e : F ≃ₗ[𝒪] (Fin n → 𝒪) := b.equivFun
  have h1 : (c • (⊤ : Submodule 𝒪 F)).map (e : F →ₗ[𝒪] (Fin n → 𝒪)) =
      c • (⊤ : Submodule 𝒪 (Fin n → 𝒪)) := by
    rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range]
  have h2 : (c • (⊤ : Submodule 𝒪 (Fin n → 𝒪))) =
      Submodule.pi Set.univ (fun _ : Fin n => (Ideal.span ({c} : Set 𝒪) : Submodule 𝒪 𝒪)) := by
    ext f
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Submodule.mem_pi, Set.mem_univ, forall_const]
    constructor
    · rintro ⟨g, rfl⟩ i
      exact Ideal.mem_span_singleton'.mpr ⟨g i, by simp [mul_comm]⟩
    · intro h
      choose d hd using fun i => Ideal.mem_span_singleton'.mp (h i)
      exact ⟨d, funext fun i => by simp [← hd i, mul_comm]⟩
  calc Module.length 𝒪 (F ⧸ (c • (⊤ : Submodule 𝒪 F)))
      = Module.length 𝒪 ((Fin n → 𝒪) ⧸ (c • (⊤ : Submodule 𝒪 (Fin n → 𝒪)))) :=
        (Submodule.Quotient.equiv _ _ e h1).length_eq
    _ = Module.length 𝒪 ((Fin n → 𝒪) ⧸
          Submodule.pi Set.univ (fun _ : Fin n => (Ideal.span ({c} : Set 𝒪) : Submodule 𝒪 𝒪))) :=
        (Submodule.quotEquivOfEq _ _ h2).length_eq
    _ = Module.length 𝒪 (Fin n → 𝒪 ⧸ (Ideal.span ({c} : Set 𝒪))) :=
        (Submodule.quotientPi _).length_eq
    _ = ∑ _i : Fin n, Module.length 𝒪 (𝒪 ⧸ Ideal.span ({c} : Set 𝒪)) :=
        Module.length_pi_of_fintype 𝒪 _
    _ = (n : ℕ∞) * Module.length 𝒪 (𝒪 ⧸ Ideal.span ({c} : Set 𝒪)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end PID

section Aug

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)
variable {M : Type x} [AddCommGroup M] [Module T M]

theorem πT_surjective : Function.Surjective πT :=
  fun c => ⟨algebraMap 𝒪 T c, πT.commutes c⟩

theorem smul_mem_torsion_of_mem_annihilator {a : T} (ha : a ∈ (RingHom.ker πT).annihilator) (n : M) :
    a • n ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT) := by
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨p, hp⟩
  rw [Submodule.mem_annihilator] at ha
  have : a * p = 0 := by simpa [smul_eq_mul] using ha p hp
  rw [smul_smul, mul_comm, this, zero_smul]

variable [Module 𝒪 M] [IsScalarTower 𝒪 T M]

theorem smul_eq_of_mem_torsion {x : M} (hx : x ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT))
    (t : T) : t • x = (πT t) • x := by
  rw [Submodule.mem_torsionBySet_iff] at hx
  have h1 : (t - algebraMap 𝒪 T (πT t)) • x = 0 := hx ⟨_, by simp [RingHom.mem_ker]⟩
  rw [sub_smul, sub_eq_zero, algebraMap_smul] at h1
  exact h1

theorem exists_mem_annihilator_ne_zero (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥) :
    ∃ e ∈ (RingHom.ker πT).annihilator, πT e ≠ 0 := by
  by_contra h
  apply hη
  rw [eq_bot_iff]
  refine (Ideal.map_le_iff_le_comap).mpr fun e he => ?_
  rw [Ideal.mem_comap]
  by_contra hne
  exact h ⟨e, he, fun h0 => hne (by rw [h0]; exact Submodule.zero_mem _)⟩

end Aug

section Gram

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪]
  [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)
  {M : Type x} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪)

noncomputable def Φ : M →ₗ[𝒪] Module.Dual 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT)) :=
  ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪).dualMap ∘ₗ B

theorem Φ_apply (m : M) (x : ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT))) :
    Φ πT B m x = B m x := rfl

theorem range_gram_eq_map :
    LinearMap.range (B.compl₁₂ ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪)
        ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪)) =
      ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪).map (Φ πT B) := by
  ext f
  simp only [LinearMap.mem_range, Submodule.mem_map, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by ext x; rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, by ext x; rfl⟩

omit [IsScalarTower 𝒪 T M] in

theorem mem_torsionI_of_apply_eq_zero (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBi : Function.Injective B) {m : M}
    (h : ∀ x ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT), B m x = 0) :
    m ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator := by
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨a, ha⟩
  have : B (a • m) = 0 := by
    ext n
    rw [hB, LinearMap.zero_apply]
    exact h _ (smul_mem_torsion_of_mem_annihilator πT ha n)
  exact hBi (this.trans (map_zero B).symm)

variable [IsDomain 𝒪]

theorem apply_eq_zero_of_mem_torsionI (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    {m x : M} (hm : m ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)
    (hx : x ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT)) : B m x = 0 := by
  obtain ⟨e, he, hπe⟩ := exists_mem_annihilator_ne_zero πT hη
  have hem : e • m = 0 := by
    rw [Submodule.mem_torsionBySet_iff] at hm
    exact hm ⟨e, he⟩
  have : πT e * B m x = 0 := by
    calc πT e * B m x = B m (πT e • x) := by rw [map_smul, smul_eq_mul]
      _ = B m (e • x) := by rw [smul_eq_of_mem_torsion πT hx e]
      _ = B (e • m) x := (hB e m x).symm
      _ = 0 := by rw [hem, map_zero, LinearMap.zero_apply]
  exact (mul_eq_zero.mp this).resolve_left hπe

theorem mem_ker_Φ_iff (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n)) (hBi : Function.Injective B) (m : M) :
    m ∈ LinearMap.ker (Φ πT B) ↔ m ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator := by
  constructor
  · intro h
    refine mem_torsionI_of_apply_eq_zero πT B hB hBi fun x hx => ?_
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp h) ⟨x, hx⟩
    rwa [Φ_apply, LinearMap.zero_apply] at this
  · intro h
    rw [LinearMap.mem_ker]
    ext x
    rw [Φ_apply, LinearMap.zero_apply]
    exact apply_eq_zero_of_mem_torsionI πT B hη hB h x.2

theorem ker_mkQ_comp_Φ (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n)) (hBi : Function.Injective B) :
    LinearMap.ker ((LinearMap.range (B.compl₁₂
        ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪)
        ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪))).mkQ ∘ₗ Φ πT B) =
      (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator).restrictScalars 𝒪 := by
  rw [Submodule.restrictScalars_sup]
  ext m
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    range_gram_eq_map, Submodule.mem_map, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, hym⟩
    refine ⟨y, hy, m - y, ?_, add_sub_cancel y m⟩
    rw [Submodule.restrictScalars_mem, ← mem_ker_Φ_iff πT B hη hB hBi, LinearMap.mem_ker, map_sub, hym, sub_self]
  · rintro ⟨y, hy, z, hz, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [Submodule.restrictScalars_mem, ← mem_ker_Φ_iff πT B hη hB hBi, LinearMap.mem_ker] at hz
    rw [map_add, hz, add_zero]

variable [IsPrincipalIdealRing 𝒪] [Module.Finite 𝒪 M] [Module.Free 𝒪 M]

theorem exists_retraction :
    ∃ p : M →ₗ[𝒪] ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT)),
      ∀ x : ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT)), p x = x := by
  set N := Submodule.torsionBySet T M ↑(RingHom.ker πT) with hN
  set N₀ : Submodule 𝒪 M := N.restrictScalars 𝒪 with hN₀

  haveI : NoZeroSMulDivisors 𝒪 (M ⧸ N₀) := by
    refine ⟨fun {c q} hcq => ?_⟩
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N₀ q
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hN₀,
      Submodule.restrictScalars_mem, hN, Submodule.mem_torsionBySet_iff] at hcq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN₀, Submodule.restrictScalars_mem, hN,
      Submodule.mem_torsionBySet_iff]
    intro p
    have h1 : c • ((p : T) • m) = 0 := by rw [smul_comm]; exact hcq p
    exact (smul_eq_zero.mp h1).resolve_left hc
  haveI : Module.Free 𝒪 (M ⧸ N₀) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N₀.mkQ (LinearMap.id) (Submodule.mkQ_surjective N₀)
  have hmem : ∀ m : M, m - s (N₀.mkQ m) ∈ N := by
    intro m
    have : N₀.mkQ (m - s (N₀.mkQ m)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  refine ⟨{ toFun := fun m => ⟨m - s (N₀.mkQ m), hmem m⟩
            map_add' := fun m m' => by ext; simp [map_add]; abel
            map_smul' := fun c m => by ext; simp [map_smul, smul_sub] }, fun x => ?_⟩
  ext
  have hx0 : N₀.mkQ (x : M) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.2
  change (x : M) - s (N₀.mkQ (x : M)) = x
  rw [hx0, map_zero, sub_zero]

theorem Φ_surjective (hBs : Function.Surjective B) : Function.Surjective (Φ πT B) := by
  intro f
  obtain ⟨p, hp⟩ := exists_retraction (𝒪 := 𝒪) πT (M := M)
  obtain ⟨m, hm⟩ := hBs (f ∘ₗ p)
  refine ⟨m, ?_⟩
  ext x
  rw [Φ_apply, hm, LinearMap.comp_apply, hp]

noncomputable def rowAEquiv (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n)) (hBb : Function.Bijective B) :
    (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) ≃ₗ[𝒪]
      (Module.Dual 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) ⧸
        LinearMap.range (B.compl₁₂
          ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪)
          ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪))) :=
  (Submodule.Quotient.restrictScalarsEquiv 𝒪 _).symm ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_Φ πT B hη hB hBb.1).symm) ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective _
      ((Submodule.mkQ_surjective _).comp (Φ_surjective πT B hBb.2))

end Gram

section LevelChange

variable {𝒪 : Type u} {T T' : Type w} [CommRing 𝒪]
  [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T']
  (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪)
  {M : Type x} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type x} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (Δ : T)
  (hji : ∀ m : M, j (i m) = Δ • m) (hΔ : πT Δ ≠ 0)
  (h℘ : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪)

def iRes : ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT)) →ₗ[𝒪]
    ↥(Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) where
  toFun x := ⟨i x, by
    have hx : i (x : M) ∈ Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) :=
      Submodule.mem_map_of_mem x.2
    rw [h℘] at hx
    exact hx⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

variable (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪)
  (hadj : ∀ (m' : M') (m : M), B (j m') m = B' m' (i m))

include hadj hji in

theorem gram_transport (x y : ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT))) :
    B' (i x) (i y) = πT Δ * B x y := by
  rw [← hadj, hji, smul_eq_of_mem_torsion πT x.2 Δ, map_smul, LinearMap.smul_apply, smul_eq_mul]

variable [IsDomain 𝒪] [Module.Free 𝒪 M]

include hji hΔ in
theorem iRes_bijective : Function.Bijective (iRes πT πT' i h℘) := by
  constructor
  · intro x y hxy
    have h1 : i (x : M) = i (y : M) := congrArg Subtype.val hxy
    have h2 : (πT Δ) • ((x : M) - y) = 0 := by
      rw [← smul_eq_of_mem_torsion πT (Submodule.sub_mem _ x.2 y.2) Δ, ← hji, map_sub, h1, sub_self,
        map_zero]
    have h3 : (x : M) - y = 0 := (smul_eq_zero.mp h2).resolve_left hΔ
    exact Subtype.ext (sub_eq_zero.mp h3)
  · intro y
    have hy : (y : M') ∈ Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) := by
      rw [h℘]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

noncomputable def eRes : ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT)) ≃ₗ[𝒪]
    ↥(Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) :=
  LinearEquiv.ofBijective (iRes πT πT' i h℘) (iRes_bijective πT πT' i j Δ hji hΔ h℘)

theorem eRes_apply (x : ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT))) :
    (eRes πT πT' i j Δ hji hΔ h℘ x : M') = i x := rfl

include hadj in

theorem map_dualMap_range_gram :
    (LinearMap.range (B'.compl₁₂
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).subtype.restrictScalars 𝒪)
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).subtype.restrictScalars 𝒪))).map
      ((eRes πT πT' i j Δ hji hΔ h℘).dualMap :
        Module.Dual 𝒪 ↥(Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) →ₗ[𝒪]
          Module.Dual 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker πT))) =
    LinearMap.range (πT Δ • B.compl₁₂
        ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪)
        ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).subtype.restrictScalars 𝒪)) := by
  set e := eRes πT πT' i j Δ hji hΔ h℘ with he
  ext f
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨f', ⟨y', rfl⟩, rfl⟩
    obtain ⟨y, rfl⟩ := e.surjective y'
    refine ⟨y, ?_⟩
    ext x
    change πT Δ • B (y : M) (x : M) = B' ((e y : _) : M') ((e x : _) : M')
    rw [eRes_apply, eRes_apply, gram_transport πT i j Δ hji B B' hadj, smul_eq_mul]
  · rintro ⟨y, rfl⟩
    refine ⟨_, ⟨e y, rfl⟩, ?_⟩
    ext x
    change B' ((e y : _) : M') ((e x : _) : M') = πT Δ • B (y : M) (x : M)
    rw [eRes_apply, eRes_apply, gram_transport πT i j Δ hji B B' hadj, smul_eq_mul]

end LevelChange

section Cokernel

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪]
  {N : Type*} [AddCommGroup N] [Module 𝒪 N]
  {D : Type*} [AddCommGroup D] [Module 𝒪 D] [Module.Finite 𝒪 D] [Module.Free 𝒪 D]

theorem length_quotient_range_smul (g : N →ₗ[𝒪] D) {c : 𝒪} (hc : c ≠ 0) :
    Module.length 𝒪 (D ⧸ LinearMap.range (c • g)) =
      Module.length 𝒪 (D ⧸ LinearMap.range g) +
        (Module.finrank 𝒪 D : ℕ∞) * Module.length 𝒪 (𝒪 ⧸ Ideal.span ({c} : Set 𝒪)) := by
  set R := LinearMap.range g with hR
  set P := LinearMap.range (c • g) with hP
  set Q : Submodule 𝒪 D := c • (⊤ : Submodule 𝒪 D) with hQ
  have hPQ : P ≤ Q := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem_pointwise_smul _ c ⊤ Submodule.mem_top

  let ψ : D ⧸ P →ₗ[𝒪] D ⧸ Q := Submodule.mapQ P Q LinearMap.id hPQ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective Q q
    exact ⟨Submodule.mkQ P f, rfl⟩

  let χ : D →ₗ[𝒪] D ⧸ P := P.mkQ ∘ₗ (c • LinearMap.id)
  have hχ : ∀ f, χ f = P.mkQ (c • f) := fun _ => rfl
  have hkerχ : LinearMap.ker χ = R := by
    ext f
    rw [LinearMap.mem_ker, hχ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hP, hR,
      LinearMap.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      rw [LinearMap.smul_apply] at hy
      exact ⟨y, (smul_right_injective D hc) hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [LinearMap.smul_apply]⟩
  have hrangeχ : LinearMap.range χ = LinearMap.ker ψ := by
    ext q
    obtain ⟨f₀, rfl⟩ := Submodule.mkQ_surjective P q
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    change (∃ f, P.mkQ (c • f) = P.mkQ f₀) ↔ Submodule.mapQ P Q LinearMap.id hPQ (Submodule.Quotient.mk f₀) = 0
    rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, hQ,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨f, hf⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hP] at hf
      obtain ⟨y, hy⟩ := hf
      refine ⟨f - g y, Submodule.mem_top, ?_⟩
      rw [LinearMap.smul_apply] at hy
      rw [smul_sub, hy, sub_sub_cancel]
    · rintro ⟨f, -, rfl⟩
      exact ⟨f, rfl⟩
  have hlen1 : Module.length 𝒪 (D ⧸ P) = Module.length 𝒪 (LinearMap.ker ψ) + Module.length 𝒪 (D ⧸ Q) :=
    Module.length_eq_add_of_exact (LinearMap.ker ψ).subtype ψ (Submodule.injective_subtype _) hψs
      (LinearMap.exact_subtype_ker_map ψ)
  have hlen2 : Module.length 𝒪 (LinearMap.ker ψ) = Module.length 𝒪 (D ⧸ R) := by
    have e1 : (D ⧸ R) ≃ₗ[𝒪] LinearMap.range χ :=
      (Submodule.quotEquivOfEq _ _ hkerχ.symm) ≪≫ₗ χ.quotKerEquivRange
    exact (e1 ≪≫ₗ LinearEquiv.ofEq _ _ hrangeχ).length_eq.symm
  rw [hlen1, hlen2, hQ, length_quotient_smul_top D c]

end Cokernel

end M4cP4PairB

open M4cP4PairB in
theorem solution
    {𝒪 : Type u} {T T' : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T']
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (πT' : T' →ₐ[𝒪] 𝒪) (hη' : (RingHom.ker πT').annihilator.map πT' ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (M' : Type x) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪) (hB' : ∀ (t : T') (m n : M'), B' (t • m) n = B' m (t • n))
    (hBb' : Function.Bijective B')
    (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (hadj : ∀ (m' : M') (m : M), B (j m') m = B' m' (i m))
    (Δ : T) (hji : ∀ m : M, j (i m) = Δ • m) (hΔ : πT Δ ≠ 0)
    (h℘ : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪) :
    Module.finrank 𝒪 (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) =
        Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) ∧
      Module.length 𝒪 (M' ⧸ (Submodule.torsionBySet T' M' ↑(RingHom.ker πT') ⊔
          Submodule.torsionBySet T' M' ↑(RingHom.ker πT').annihilator)) =
        Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
          Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) +
        (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
          Module.length 𝒪 (𝒪 ⧸ Ideal.span {πT Δ}) := by
  set N : Submodule T M := Submodule.torsionBySet T M ↑(RingHom.ker πT) with hN

  let eN : ↥(N.restrictScalars 𝒪) ≃ₗ[𝒪] ↥N :=
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => ⟨p.1, p.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Free 𝒪 ↥N := Module.Free.of_equiv eN
  haveI : Module.Finite 𝒪 ↥N := Module.Finite.equiv eN
  let e := eRes πT πT' i j Δ hji hΔ h℘
  refine ⟨e.finrank_eq.symm, ?_⟩
  have hA := (rowAEquiv πT B hη hB hBb).length_eq
  have hA' := (rowAEquiv πT' B' hη' hB' hBb').length_eq
  have hQ1 := (Submodule.Quotient.equiv _ _ e.dualMap
    (map_dualMap_range_gram πT πT' i j Δ hji hΔ h℘ B B' hadj)).length_eq
  have hck := length_quotient_range_smul (D := Module.Dual 𝒪 ↥N)
    (B.compl₁₂ (N.subtype.restrictScalars 𝒪) (N.subtype.restrictScalars 𝒪)) hΔ
  have hfr : Module.finrank 𝒪 (Module.Dual 𝒪 ↥N) = Module.finrank 𝒪 ↥N :=
    (Module.finBasis 𝒪 ↥N).toDualEquiv.finrank_eq.symm
  rw [hA', hQ1, hck, hfr, ← hA]

end S_Module_length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq
end P2MW
export P2MW.S_Module_length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq (solution)
