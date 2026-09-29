-- Prove2me | solution 1 for IharaTower.iharaClauseAt_and_isIharaDataAt_cornerRung
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/636cd6e4-c15f-52e5-b50a-b9ea9bf89b54

import Definitions.Def_HeckeModule_IharaDataAt
import Theorems.Thm_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs
import Theorems.Thm_IharaLemma_map_codRestrict_eq_of_residual
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_iharaClauseAt_and_isIharaDataAt_cornerRung

set_option autoImplicit false

namespace IharaTowerSolGlue

open IharaTower IharaLemma

section Abstract

variable {𝒪 : Type} [CommRing 𝒪]
  {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']

section Domain

variable [IsDomain 𝒪]

private theorem smul_eq_zero_free {X : Type} [AddCommGroup X] [Module 𝒪 X] [Module.Free 𝒪 X]
    {a : 𝒪} (ha : a ≠ 0) {x : X} (h : a • x = 0) : x = 0 := by
  classical
  let b := Module.Free.chooseBasis 𝒪 X
  refine b.ext_elem fun k => ?_
  have hk := congrArg (fun y => b.repr y k) h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at hk
  rcases mul_eq_zero.mp hk with h0 | h0
  · exact absurd h0 ha
  · rw [h0, map_zero, Finsupp.zero_apply]

private theorem isTorsionFree_free {X : Type} [AddCommGroup X] [Module 𝒪 X] [Module.Free 𝒪 X] :
    Module.IsTorsionFree 𝒪 X :=
  Module.IsTorsionFree.of_smul_eq_zero fun a x h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (smul_eq_zero_free ha h)

end Domain

private theorem right_sep [Module.Free 𝒪 M] (P : LevelPairing (𝒪 := 𝒪) T M)
    {y : M} (h : ∀ m, P.B m y = 0) : y = 0 := by
  classical
  let b := Module.Free.chooseBasis 𝒪 M
  refine b.ext_elem fun k => ?_
  obtain ⟨m, hm⟩ := P.perfect.2 (b.coord k)
  have hk := h m
  rw [hm] at hk
  rw [map_zero, Finsupp.zero_apply]
  simpa [Module.Basis.coord_apply] using hk

private theorem right_sep' [Module.Free 𝒪 M'] (P' : LevelPairing (𝒪 := 𝒪) T' M')
    {y : M'} (h : ∀ m, P'.B m y = 0) : y = 0 := by
  classical
  let b := Module.Free.chooseBasis 𝒪 M'
  refine b.ext_elem fun k => ?_
  obtain ⟨m, hm⟩ := P'.perfect.2 (b.coord k)
  have hk := h m
  rw [hm] at hk
  rw [map_zero, Finsupp.zero_apply]
  simpa [Module.Basis.coord_apply] using hk

private theorem B_smul_top_torsion (P : LevelPairing (𝒪 := 𝒪) T M) (𝔭 : Ideal T) {x : M}
    (hx : x ∈ 𝔭 • (⊤ : Submodule T M)) {m : M} (hm : m ∈ Submodule.torsionBySet T M ↑𝔭) :
    P.B x m = 0 := by
  refine Submodule.smul_induction_on hx (fun t ht y _ => ?_) (fun x y hx hy => ?_)
  · have h0 : t • m = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hm ⟨t, ht⟩
    rw [P.selfAdjoint, h0, map_zero]
  · rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

private theorem B_smul_top_torsion' (P' : LevelPairing (𝒪 := 𝒪) T' M') (𝔭' : Ideal T') {x : M'}
    (hx : x ∈ 𝔭' • (⊤ : Submodule T' M')) {m : M'}
    (hm : m ∈ Submodule.torsionBySet T' M' ↑𝔭') : P'.B x m = 0 := by
  refine Submodule.smul_induction_on hx (fun t ht y _ => ?_) (fun x y hx hy => ?_)
  · have h0 : t • m = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hm ⟨t, ht⟩
    rw [P'.selfAdjoint, h0, map_zero]
  · rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

private theorem mem_torsion_of_B_smul_top [Module.Free 𝒪 M']
    (P' : LevelPairing (𝒪 := 𝒪) T' M') (𝔭' : Ideal T') {y : M'}
    (h : ∀ x ∈ 𝔭' • (⊤ : Submodule T' M'), P'.B x y = 0) :
    y ∈ Submodule.torsionBySet T' M' ↑𝔭' := by
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨t, ht⟩
  refine right_sep' P' fun z => ?_
  show P'.B z (t • y) = 0
  rw [← P'.selfAdjoint]
  exact h _ (Submodule.smul_mem_smul ht Submodule.mem_top)

variable {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}

private theorem i_smul [Module.Free 𝒪 M'] (D : RungDatum T T' M M' P P')
    (hjeq : ∀ (t' : T') (m' : M'), D.j (t' • m') = D.res t' • D.j m') (t' : T') (m : M) :
    D.i (D.res t' • m) = t' • D.i m := by
  have key : ∀ m', P'.B m' (D.i (D.res t' • m)) = P'.B m' (t' • D.i m) := fun m' => by
    rw [← D.adjoint, ← P.selfAdjoint, ← hjeq, D.adjoint, P'.selfAdjoint]
  have h0 := right_sep' P' (y := D.i (D.res t' • m) - t' • D.i m)
    (fun m' => by rw [map_sub, key, sub_self])
  exact sub_eq_zero.mp h0

private theorem map_torsion_le [Module.Free 𝒪 M'] (D : RungDatum T T' M M' P P')
    (hjeq : ∀ (t' : T') (m' : M'), D.j (t' • m') = D.res t' • D.j m') (πT : T →ₐ[𝒪] 𝒪) :
    Submodule.map D.i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) ≤
      (Submodule.torsionBySet T' M' ↑(RingHom.ker (πT.comp D.res))).restrictScalars 𝒪 := by
  rintro _ ⟨m, hm, rfl⟩
  rw [Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff]
  rintro ⟨t', ht'⟩
  have hres : D.res t' ∈ RingHom.ker πT := by
    simpa only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.comp_apply] using ht'
  have h0 : D.res t' • m = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hm ⟨D.res t', hres⟩
  show t' • D.i m = 0
  rw [← i_smul D hjeq, h0, map_zero]

private theorem smul_top_le_comap (D : RungDatum T T' M M' P P')
    (hjeq : ∀ (t' : T') (m' : M'), D.j (t' • m') = D.res t' • D.j m') (πT : T →ₐ[𝒪] 𝒪) :
    ((RingHom.ker (πT.comp D.res)) • (⊤ : Submodule T' M')).restrictScalars 𝒪 ≤
      Submodule.comap D.j (((RingHom.ker πT) • (⊤ : Submodule T M)).restrictScalars 𝒪) := by
  intro m' hm'
  rw [Submodule.restrictScalars_mem] at hm'
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
  refine Submodule.smul_induction_on hm' (fun t' ht' n _ => ?_) (fun x y hx hy => ?_)
  · rw [hjeq]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    simpa only [RingHom.mem_ker, AlgHom.comp_apply] using ht'
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

section Sat

variable [IsDomain 𝒪] [Module.Free 𝒪 M']

private theorem pow_sat (D : RungDatum T T' M M' P P') {ϖ : 𝒪}
    (hres : ∀ (v : M) (x : M'), D.i v = ϖ • x → ∃ v₁, v = ϖ • v₁) (hϖ : ϖ ≠ 0) :
    ∀ (n : ℕ) (v : M) (x : M'), D.i v = ϖ ^ n • x → ∃ w, v = ϖ ^ n • w ∧ D.i w = x := by
  intro n
  induction n with
  | zero =>
    intro v x h
    exact ⟨v, by rw [pow_zero, one_smul], by rw [h, pow_zero, one_smul]⟩
  | succ n ih =>
    intro v x h
    rw [pow_succ', mul_smul] at h
    obtain ⟨v₁, rfl⟩ := hres v (ϖ ^ n • x) h
    rw [map_smul] at h
    have h' : D.i v₁ = ϖ ^ n • x := by
      have := smul_eq_zero_free (X := M') hϖ (x := D.i v₁ - ϖ ^ n • x)
        (by rw [smul_sub, h, sub_self])
      exact sub_eq_zero.mp this
    obtain ⟨w, rfl, hw⟩ := ih v₁ x h'
    exact ⟨w, by rw [pow_succ', mul_smul], hw⟩

end Sat

section DVR

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

private theorem eq_zero_of_forall_pow_dvd {ϖ : 𝒪} (hϖ : Irreducible ϖ) {x : 𝒪}
    (h : ∀ n : ℕ, ϖ ^ n ∣ x) : x = 0 := by
  by_contra hx
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨c, hc⟩ := h (k + 1)
  have h1 : ϖ ^ k * (u : 𝒪) = ϖ ^ k * (ϖ * c) := by
    rw [mul_comm (ϖ ^ k) (u : 𝒪), hc]; ring
  have h2 : (u : 𝒪) = ϖ * c := mul_left_cancel₀ (pow_ne_zero k hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_dvd_unit ⟨c, h2⟩ u.isUnit)

variable [Module.Free 𝒪 M'] [Module.Free 𝒪 M]

private theorem i_injective (D : RungDatum T T' M M' P P') {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : M) (x : M'), D.i v = ϖ • x → ∃ v₁, v = ϖ • v₁) :
    Function.Injective D.i := by
  classical
  intro v₁ v₂ h
  rw [← sub_eq_zero] at h ⊢
  rw [← map_sub] at h
  set v := v₁ - v₂
  have hv : ∀ n : ℕ, ∃ w, v = ϖ ^ n • w := fun n => by
    obtain ⟨w, hw, -⟩ := pow_sat D hres hϖ.ne_zero n v 0 (by rw [h, smul_zero])
    exact ⟨w, hw⟩
  let b := Module.Free.chooseBasis 𝒪 M
  refine b.ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine eq_zero_of_forall_pow_dvd hϖ fun n => ?_
  obtain ⟨w, hw⟩ := hv n
  exact ⟨b.repr w k, by rw [hw, map_smul, Finsupp.smul_apply, smul_eq_mul]⟩

end DVR

section Count

variable [IsDomain 𝒪]

private theorem exists_smul_mem_of_finrank_le {X : Type} [AddCommGroup X] [Module 𝒪 X]
    {K L : Submodule 𝒪 X} [Module.Finite 𝒪 L] (hKL : K ≤ L)
    (h : Module.finrank 𝒪 L ≤ Module.finrank 𝒪 K) {x : X} (hx : x ∈ L) :
    ∃ a : 𝒪, a ≠ 0 ∧ a • x ∈ K := by
  let K' : Submodule 𝒪 L := Submodule.comap L.subtype K
  have hK' : Module.finrank 𝒪 K' = Module.finrank 𝒪 K :=
    (Submodule.comapSubtypeEquivOfLe hKL).finrank_eq
  have hq : Module.finrank 𝒪 (L ⧸ K') = 0 := by
    have := Submodule.finrank_quotient_add_finrank K'
    omega
  obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.mp hq (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax

end Count

section Clause

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [Module.Free 𝒪 M] [Module.Free 𝒪 M'] [Module.Finite 𝒪 M']

private theorem torsion_surj (D : RungDatum T T' M M' P P') (πT : T →ₐ[𝒪] 𝒪) {ϖ : 𝒪}
    (hϖ : Irreducible ϖ)
    (hres : ∀ (v : M) (x : M'), D.i v = ϖ • x → ∃ v₁, v = ϖ • v₁)
    (hjeq : ∀ (t' : T') (m' : M'), D.j (t' • m') = D.res t' • D.j m')
    (hrank : Module.finrank 𝒪
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker (πT.comp D.res))).restrictScalars 𝒪)
      ≤ Module.finrank 𝒪
        ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
    ∀ w ∈ (Submodule.torsionBySet T' M' ↑(RingHom.ker (πT.comp D.res))).restrictScalars 𝒪,
      ∃ m ∈ (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪, D.i m = w := by
  have htop : ∀ x : M', x ∈ (cornerSubmodule (M := M') (1 : T')).restrictScalars 𝒪 := fun x => by
    simp [cornerSubmodule]
  have hA : ∀ (c : 𝒪) (x : M), c ≠ 0 →
      c • x ∈ (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪 →
      x ∈ (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪 := by
    intro c x hc hcx
    rw [Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff] at hcx ⊢
    intro t
    have h1 : c • ((t : T) • x) = 0 := by rw [smul_comm]; exact hcx t
    exact smul_eq_zero_free hc h1
  have hle : Submodule.map (LinearMap.codRestrict
        ((cornerSubmodule (M := M') (1 : T')).restrictScalars 𝒪) D.i fun v => htop (D.i v))
        ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) ≤
      Submodule.comap ((cornerSubmodule (M := M') (1 : T')).restrictScalars 𝒪).subtype
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker (πT.comp D.res))).restrictScalars 𝒪) := by
    rintro _ ⟨m, hm, rfl⟩
    exact map_torsion_le D hjeq πT (Submodule.mem_map_of_mem hm)
  have hrank' : Module.finrank 𝒪
      (Submodule.comap ((cornerSubmodule (M := M') (1 : T')).restrictScalars 𝒪).subtype
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker (πT.comp D.res))).restrictScalars 𝒪)) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) := by
    have hX'le : (Submodule.torsionBySet T' M' ↑(RingHom.ker (πT.comp D.res))).restrictScalars 𝒪 ≤
        (cornerSubmodule (M := M') (1 : T')).restrictScalars 𝒪 := fun x _ => htop x
    rw [(Submodule.comapSubtypeEquivOfLe hX'le).finrank_eq]
    exact hrank
  have heq := IharaLemma.map_codRestrict_eq_of_residual D.i (1 : T') (fun v => htop (D.i v))
    (i_injective D hϖ hres) hϖ hres hA hle hrank'
  intro w hw
  have hw' : (⟨w, htop w⟩ : ((cornerSubmodule (M := M') (1 : T')).restrictScalars 𝒪)) ∈
      Submodule.comap ((cornerSubmodule (M := M') (1 : T')).restrictScalars 𝒪).subtype
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker (πT.comp D.res))).restrictScalars 𝒪) := hw
  rw [← heq] at hw'
  obtain ⟨m, hm, hmw⟩ := hw'
  exact ⟨m, hm, congrArg Subtype.val hmw⟩

end Clause

section Data

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [Module.Finite 𝒪 M']

private theorem exists_B_eq (P' : LevelPairing (𝒪 := 𝒪) T' M') (W : Submodule 𝒪 M')
    (hWsat : ∀ (a : 𝒪) (x : M'), a ≠ 0 → a • x ∈ W → x ∈ W) (f : ↥W →ₗ[𝒪] 𝒪) :
    ∃ m' : M', ∀ w : ↥W, P'.B m' w = f w := by
  haveI : Module.IsTorsionFree 𝒪 (M' ⧸ W) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a q h => ?_
    by_cases ha : a = 0
    · exact Or.inl ha
    refine Or.inr ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    rw [Submodule.Quotient.mk_eq_zero]
    exact hWsat a x ha h
  haveI : Module.Free 𝒪 (M' ⧸ W) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property W.mkQ LinearMap.id W.mkQ_surjective
  have hπ : ∀ m : M', ((LinearMap.id : M' →ₗ[𝒪] M') - s.comp W.mkQ) m ∈ W := fun m => by
    have hsm : Submodule.Quotient.mk (p := W) (s (Submodule.Quotient.mk m)) =
        Submodule.Quotient.mk m := by
      simpa using LinearMap.congr_fun hs (Submodule.Quotient.mk m)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hsm, sub_self]
  obtain ⟨m', hm'⟩ :=
    P'.perfect.2 (f.comp (LinearMap.codRestrict W ((LinearMap.id : M' →ₗ[𝒪] M') - s.comp W.mkQ) hπ))
  refine ⟨m', fun w => ?_⟩
  rw [hm', LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  rw [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr w.2, map_zero, sub_zero]

variable [Module.Free 𝒪 M']

private theorem data_hard (D : RungDatum T T' M M' P P') (πT : T →ₐ[𝒪] 𝒪)
    (hclause : IharaClauseAt D πT (πT.comp D.res))
    (hsat' : ∀ (a : 𝒪) (m' : M'), a ≠ 0 →
      a • m' ∈ (RingHom.ker (πT.comp D.res) • ⊤ : Submodule T' M').restrictScalars 𝒪 →
      m' ∈ (RingHom.ker (πT.comp D.res) • ⊤ : Submodule T' M').restrictScalars 𝒪) :
    Submodule.comap D.j (((RingHom.ker πT) • (⊤ : Submodule T M)).restrictScalars 𝒪) ≤
      ((RingHom.ker (πT.comp D.res)) • (⊤ : Submodule T' M')).restrictScalars 𝒪 := by
  classical
  set 𝔭' : Ideal T' := RingHom.ker (πT.comp D.res) with h𝔭'
  set W : Submodule 𝒪 M' := (Submodule.torsionBySet T' M' ↑𝔭').restrictScalars 𝒪 with hW
  set C : Submodule 𝒪 M' := (𝔭' • (⊤ : Submodule T' M')).restrictScalars 𝒪 with hC
  haveI : Module.IsTorsionFree 𝒪 M' := isTorsionFree_free
  haveI : IsNoetherian 𝒪 M' := inferInstance

  let Φ : M' →ₗ[𝒪] (↥W →ₗ[𝒪] 𝒪) := (LinearMap.lcomp 𝒪 𝒪 W.subtype).comp P'.B
  let Ψ : M' →ₗ[𝒪] (↥C →ₗ[𝒪] 𝒪) := (LinearMap.lcomp 𝒪 𝒪 C.subtype).comp P'.B.flip
  have hΦ : ∀ (m' : M') (w : W), Φ m' w = P'.B m' w := fun _ _ => rfl
  have hΨ : ∀ (y : M') (x : C), Ψ y x = P'.B x y := fun _ _ => rfl

  have hCΦ : C ≤ LinearMap.ker Φ := fun y hy => by
    rw [LinearMap.mem_ker]
    ext w
    rw [hΦ, LinearMap.zero_apply]
    exact B_smul_top_torsion' P' 𝔭' hy w.2

  have hΨW : LinearMap.ker Ψ ≤ W := fun y hy => by
    rw [LinearMap.mem_ker] at hy
    rw [hW, Submodule.restrictScalars_mem]
    refine mem_torsion_of_B_smul_top P' 𝔭' fun x hx => ?_
    have := LinearMap.congr_fun hy ⟨x, hx⟩
    rwa [hΨ, LinearMap.zero_apply] at this

  have hWsat : ∀ (a : 𝒪) (x : M'), a ≠ 0 → a • x ∈ W → x ∈ W := by
    intro a x ha hx
    rw [hW, Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff] at hx ⊢
    rintro ⟨t, ht⟩
    have h1 : a • (t • x) = 0 := by rw [smul_comm]; exact hx ⟨t, ht⟩
    exact smul_eq_zero_free ha h1
  have hΦsurj : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro f
    obtain ⟨m', hm'⟩ := exists_B_eq P' W hWsat f
    exact ⟨m', LinearMap.ext fun w => by rw [hΦ, hm']⟩

  have hrnΦ := Submodule.finrank_quotient_add_finrank (LinearMap.ker Φ)
  have hrnΨ := Submodule.finrank_quotient_add_finrank (LinearMap.ker Ψ)
  have hqΦ : Module.finrank 𝒪 (M' ⧸ LinearMap.ker Φ) = Module.finrank 𝒪 W := by
    rw [(LinearMap.quotKerEquivRange Φ).finrank_eq, hΦsurj, finrank_top,
      Module.finrank_linearMap_self]
  have hqΨ : Module.finrank 𝒪 (M' ⧸ LinearMap.ker Ψ) ≤ Module.finrank 𝒪 C := by
    rw [(LinearMap.quotKerEquivRange Ψ).finrank_eq]
    calc Module.finrank 𝒪 (LinearMap.range Ψ) ≤ Module.finrank 𝒪 (↥C →ₗ[𝒪] 𝒪) :=
          Submodule.finrank_le _
      _ = Module.finrank 𝒪 C := Module.finrank_linearMap_self 𝒪 𝒪 ↥C
  have h1 : Module.finrank 𝒪 (LinearMap.ker Ψ) ≤ Module.finrank 𝒪 W := Submodule.finrank_mono hΨW
  have h2 : Module.finrank 𝒪 C ≤ Module.finrank 𝒪 (LinearMap.ker Φ) := Submodule.finrank_mono hCΦ
  have hcount : Module.finrank 𝒪 (LinearMap.ker Φ) ≤ Module.finrank 𝒪 C := by omega

  have hcl : Submodule.map D.i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪)
      = W := hclause
  intro m' hm'
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hm'
  have hker : m' ∈ LinearMap.ker Φ := by
    rw [LinearMap.mem_ker]
    ext w
    rw [hΦ, LinearMap.zero_apply]
    have hw : (w : M') ∈
        Submodule.map D.i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) := by
      rw [hcl]; exact w.2
    obtain ⟨v, hv, hvw⟩ := hw
    rw [← hvw, ← D.adjoint]
    exact B_smul_top_torsion P _ hm' hv
  obtain ⟨a, ha, hamem⟩ := exists_smul_mem_of_finrank_le hCΦ hcount hker
  exact hsat' a m' ha hamem

end Data

end Abstract

end IharaTowerSolGlue

open IharaLemma IharaTower.RungAssembly in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup V'] [Module 𝒪 V']
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 V] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋 V] [IsScalarTower 𝒪 𝕋' V']
    (S : IdempotentSplitting 𝕋) (S' : IdempotentSplitting 𝕋') (i₀ : Fin S.n) (i₀' : Fin S'.n)
    (P : IharaTower.LevelPairing (𝒪 := 𝒪) (S.CornerRing i₀)
      ↥(cornerSubmodule (M := V) (S.e i₀)))
    (P' : IharaTower.LevelPairing (𝒪 := 𝒪) (S'.CornerRing i₀')
      ↥(cornerSubmodule (M := V') (S'.e i₀')))
    {n : ℕ}
    (L : LegDatum (T := S.CornerRing i₀) (T' := S'.CornerRing i₀')
      (M := ↥(cornerSubmodule (M := V) (S.e i₀)))
      (M' := ↥(cornerSubmodule (M := V') (S'.e i₀')))
      (𝒪 := 𝒪) P P' n)
    (c : Fin n → S.CornerRing i₀) (res : S'.CornerRing i₀' →ₐ[𝒪] S.CornerRing i₀)
    (πT : S.CornerRing i₀ →ₐ[𝒪] 𝒪)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := V) (S.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := V) (S.e i₀))]
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := V') (S'.e i₀'))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := V') (S'.e i₀'))]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : ↥(cornerSubmodule (M := V) (S.e i₀)))
      (x : ↥(cornerSubmodule (M := V') (S'.e i₀'))),
      iComb L c v = ϖ • x → ∃ v₁, v = ϖ • v₁)
    (hjeq : ∀ (t' : S'.CornerRing i₀') (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))),
      jComb L c (t' • m') = res t' • jComb L c m')
    (hsat' : ∀ (a : 𝒪) (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))), a ≠ 0 →
      a • m' ∈ (RingHom.ker (πT.comp res) • ⊤ :
        Submodule (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))).restrictScalars 𝒪 →
      m' ∈ (RingHom.ker (πT.comp res) • ⊤ :
        Submodule (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))).restrictScalars 𝒪)
    (hrank : Module.finrank 𝒪
        ((Submodule.torsionBySet (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))
          ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪)
      ≤ Module.finrank 𝒪
        ((Submodule.torsionBySet (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀))
          ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
    IharaTower.IharaClauseAt (IharaTower.cornerRung S S' i₀ i₀' P P' L c res)
      πT (πT.comp res) ∧
    IharaTower.IsIharaDataAt (IharaTower.cornerRung S S' i₀ i₀' P P' L c res)
      πT (πT.comp res) := by
  have hclause : IharaTower.IharaClauseAt (IharaTower.cornerRung S S' i₀ i₀' P P' L c res)
      πT (πT.comp res) :=
    IharaTower.RungAssembly.iharaClauseAt_rungDatumOfLegs L c res πT
      (fun t' m =>
        IharaTowerSolGlue.i_smul (IharaTower.cornerRung S S' i₀ i₀' P P' L c res) hjeq t' m)
      (IharaTowerSolGlue.torsion_surj (IharaTower.cornerRung S S' i₀ i₀' P P' L c res) πT hϖ hres
        hjeq hrank)
  refine ⟨hclause, ⟨le_antisymm ?_ ?_⟩⟩
  · exact IharaTowerSolGlue.data_hard (IharaTower.cornerRung S S' i₀ i₀' P P' L c res) πT
      hclause hsat'
  · exact IharaTowerSolGlue.smul_top_le_comap (IharaTower.cornerRung S S' i₀ i₀' P P' L c res)
      hjeq πT

end S_IharaTower_iharaClauseAt_and_isIharaDataAt_cornerRung
end P2MW
export P2MW.S_IharaTower_iharaClauseAt_and_isIharaDataAt_cornerRung (solution)
