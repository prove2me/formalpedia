-- Prove2me | solution 1 for ModPForms.card_le_finrank_modPCusp_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/569ef063-3774-5cf8-8681-9d4a39c9fb1e

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_ModularForm_finiteDimensional_and_finrank_le_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

namespace RedRankCusp

section QCoeff

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)

theorem hΓ (N : ℕ) : (1 : ℝ) ∈ (Γ₀(N)).strictPeriods := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

theorem qCoeff_add (f g : CuspForm Γ₀(N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n = ModularFormClass.qCoeff (⇑f) n + ModularFormClass.qCoeff (⇑g) n := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (hΓ N) f g, map_add]

theorem qCoeff_zero (n : ℕ) : ModularFormClass.qCoeff (⇑(0 : CuspForm Γ₀(N) k)) n = 0 := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm Γ₀(N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) n = c * ModularFormClass.qCoeff (⇑f) n := by
  unfold ModularFormClass.qCoeff
  rw [show (⇑(c • f) : ℍ → ℂ) = c • (⇑f) from by ext z; rfl,
    ModularForm.qExpansion_smul one_pos (hΓ N) c f, map_smul, smul_eq_mul]

noncomputable def coeffL (N : ℕ) (k : ℤ) (n : ℕ) : CuspForm Γ₀(N) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := qCoeff_add f g n
  map_smul' c f := qCoeff_smul c f n

@[scoped simp] theorem coeffL_apply (n : ℕ) (f : CuspForm Γ₀(N) k) :
    coeffL N k n f = ModularFormClass.qCoeff (⇑f) n := rfl

theorem eq_zero_of_forall_qCoeff (f : CuspForm Γ₀(N) k) (h : ∀ n, ModularFormClass.qCoeff (⇑f) n = 0) : f = 0 :=
  ModularFormClass.eq_of_forall_qCoeff_eq (hΓ N) fun n => by rw [h n, qCoeff_zero]

end QCoeff

section Window

variable {L V : Type*} [Field L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]

def winKer (c : ℕ → V →ₗ[L] L) (n : ℕ) : Submodule L V where
  carrier := {v | ∀ m < n, c m v = 0}
  add_mem' {v w} hv hw m hm := by rw [map_add, hv m hm, hw m hm, add_zero]
  zero_mem' m _ := map_zero _
  smul_mem' a v hv m hm := by rw [map_smul, hv m hm, smul_zero]

omit [FiniteDimensional L V] in
theorem winKer_antitone (c : ℕ → V →ₗ[L] L) : Antitone (winKer c) :=
  fun _ _ hnm v hv m hm => hv m (lt_of_lt_of_le hm hnm)

theorem exists_window (c : ℕ → V →ₗ[L] L) (hc : ∀ v, (∀ n, c n v = 0) → v = 0) :
    ∃ n₀ : ℕ, ∀ v, (∀ m < n₀, c m v = 0) → v = 0 := by
  obtain ⟨n₀, hn₀⟩ := IsArtinian.monotone_stabilizes
    (⟨fun n => OrderDual.toDual (winKer c n), fun a b h => winKer_antitone c h⟩ : ℕ →o (Submodule L V)ᵒᵈ)
  refine ⟨n₀, fun v hv => hc v fun n => ?_⟩
  have hmem : v ∈ winKer c (max n₀ (n + 1)) := by
    have e := hn₀ (max n₀ (n + 1)) (le_max_left _ _)
    have e' : winKer c n₀ = winKer c (max n₀ (n + 1)) := congrArg OrderDual.ofDual e
    rw [← e']; exact hv
  exact hmem n (lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _))

end Window

end RedRankCusp
p2m_reactivate "P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.RedRankCusp"

namespace RedRankCusp

section Lattice

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)
local notation "MF" => CuspForm Γ₀(N) k

def latt (W : Submodule ℂ MF) : Submodule ℤ MF where
  carrier := {v | v ∈ W ∧ ∀ n, ∃ m : ℤ, ModularFormClass.qCoeff (⇑v) n = m}
  add_mem' {v w} hv hw := ⟨W.add_mem hv.1 hw.1, fun n => by
    obtain ⟨a, ha⟩ := hv.2 n; obtain ⟨b, hb⟩ := hw.2 n
    exact ⟨a + b, by rw [qCoeff_add, ha, hb, Int.cast_add]⟩⟩
  zero_mem' := ⟨W.zero_mem, fun n => ⟨0, by rw [qCoeff_zero, Int.cast_zero]⟩⟩
  smul_mem' z v hv := ⟨by rw [← Int.cast_smul_eq_zsmul ℂ]; exact W.smul_mem _ hv.1, fun n => by
    obtain ⟨a, ha⟩ := hv.2 n
    exact ⟨z * a, by rw [← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul, ha, Int.cast_mul]⟩⟩

theorem mem_latt {W : Submodule ℂ MF} {v : MF} :
    v ∈ latt W ↔ v ∈ W ∧ ∀ n, ∃ m : ℤ, ModularFormClass.qCoeff (⇑v) n = m := Iff.rfl

noncomputable def ic {W : Submodule ℂ MF} (v : latt W) (n : ℕ) : ℤ := ((mem_latt.mp v.2).2 n).choose

theorem ic_spec {W : Submodule ℂ MF} (v : latt W) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(v : MF)) n = (ic v n : ℂ) := ((mem_latt.mp v.2).2 n).choose_spec

theorem ic_eq_of_qCoeff_eq {W : Submodule ℂ MF} (v : latt W) (n : ℕ) (m : ℤ)
    (h : ModularFormClass.qCoeff (⇑(v : MF)) n = m) : ic v n = m :=
  Int.cast_injective (α := ℂ) ((ic_spec v n).symm.trans h)

theorem ic_add {W : Submodule ℂ MF} (v w : latt W) (n : ℕ) : ic (v + w) n = ic v n + ic w n :=
  ic_eq_of_qCoeff_eq _ _ _ (by
    rw [Submodule.coe_add, qCoeff_add, ic_spec, ic_spec, Int.cast_add])

theorem ic_zsmul {W : Submodule ℂ MF} (z : ℤ) (v : latt W) (n : ℕ) : ic (z • v) n = z * ic v n :=
  ic_eq_of_qCoeff_eq _ _ _ (by
    rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul, ic_spec, Int.cast_mul])

theorem ic_sum {W : Submodule ℂ MF} {J : Type*} (s : Finset J) (g : J → latt W) (n : ℕ) :
    ic (∑ j ∈ s, g j) n = ∑ j ∈ s, ic (g j) n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ic_eq_of_qCoeff_eq _ _ _ (by rw [Finset.sum_empty, Submodule.coe_zero, qCoeff_zero, Finset.sum_empty, Int.cast_zero])
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ic_add, ih]

noncomputable def icL (W : Submodule ℂ MF) : latt W →ₗ[ℤ] (ℕ → ℤ) where
  toFun v n := ic v n
  map_add' v w := funext fun n => ic_add v w n
  map_smul' z v := funext fun n => by rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, ic_zsmul]

theorem latt_saturated {W : Submodule ℂ MF} (v : latt W) (m : ℤ) (hm : m ≠ 0) (h : ∀ n, m ∣ ic v n) :
    ∃ w : latt W, v = m • w := by
  have hW : ((m : ℂ)⁻¹ • (v : MF)) ∈ latt W := by
    refine ⟨W.smul_mem _ (mem_latt.mp v.2).1, fun n => ?_⟩
    obtain ⟨c, hc⟩ := h n
    refine ⟨c, ?_⟩
    rw [qCoeff_smul, ic_spec, hc, Int.cast_mul, ← mul_assoc, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hm), one_mul]
  refine ⟨⟨_, hW⟩, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_inv_cancel₀ (Int.cast_ne_zero.mpr hm), one_smul]

theorem exists_window_of (W : Submodule ℂ MF) [FiniteDimensional ℂ W] :
    ∃ n₀ : ℕ, ∀ v ∈ W, (∀ m < n₀, ModularFormClass.qCoeff (⇑v) m = 0) → v = 0 := by
  obtain ⟨n₀, h⟩ := exists_window (V := W) (fun n => (coeffL N k n).comp W.subtype) (fun v hv =>
    Subtype.ext (eq_zero_of_forall_qCoeff (v : MF) fun n => hv n))
  exact ⟨n₀, fun v hv h0 => congrArg Subtype.val (h ⟨v, hv⟩ fun m hm => h0 m hm)⟩

theorem latt_finite_free (W : Submodule ℂ MF) [FiniteDimensional ℂ W] :
    Module.Finite ℤ (latt W) ∧ Module.Free ℤ (latt W) := by
  obtain ⟨n₀, hn₀⟩ := exists_window_of (N := N) (k := k) W
  let e : latt W →ₗ[ℤ] (Fin n₀ → ℤ) := (LinearMap.funLeft ℤ ℤ (Fin.val : Fin n₀ → ℕ)).comp (icL W)
  have hinj : Function.Injective e := by
    intro v w hvw
    rw [← sub_eq_zero]
    apply Subtype.ext
    refine hn₀ _ (mem_latt.mp (v - w).2).1 fun m hm => ?_
    have := congrFun hvw ⟨m, hm⟩
    change ic v m = ic w m at this
    rw [Submodule.coe_sub, show ((v : MF) - (w : MF)) = (v : MF) + (-1 : ℂ) • (w : MF) by rw [neg_one_smul, sub_eq_add_neg],
      qCoeff_add, qCoeff_smul, ic_spec, ic_spec, this]
    ring
  haveI : Module.Finite ℤ (latt W) := Module.Finite.of_injective e hinj
  haveI : NoZeroSMulDivisors ℤ (latt W) := by
    refine ⟨fun {z v} h => ?_⟩
    by_cases hz : z = 0
    · exact Or.inl hz
    · right
      have h2 : e (z • v) = 0 := by rw [h, map_zero]
      rw [map_smul] at h2
      exact hinj ((smul_eq_zero.mp h2).resolve_left hz |>.trans (map_zero e).symm)
  exact ⟨inferInstance, Module.free_of_finite_type_torsion_free'⟩

end Lattice
p2m_reactivate "P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.RedRankCusp"

end RedRankCusp
p2m_reactivate "P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.RedRankCusp"

namespace RedRankCusp

section Reduction

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)
local notation "MF" => CuspForm Γ₀(N) k

noncomputable def red (F : Type*) [CommRing F] {W : Submodule ℂ MF} (v : latt W) : PowerSeries F :=
  PowerSeries.mk fun n => (ic v n : F)

@[scoped simp] theorem coeff_red (F : Type*) [CommRing F] {W : Submodule ℂ MF} (v : latt W) (n : ℕ) :
    PowerSeries.coeff n (red F v) = (ic v n : F) := by
  rw [red, PowerSeries.coeff_mk]

theorem red_add (F : Type*) [CommRing F] {W : Submodule ℂ MF} (v w : latt W) : red F (v + w) = red F v + red F w := by
  ext n; simp only [coeff_red, map_add, ic_add, Int.cast_add]

theorem red_zsmul (F : Type*) [CommRing F] {W : Submodule ℂ MF} (z : ℤ) (v : latt W) : red F (z • v) = (z : F) • red F v := by
  ext n; simp only [coeff_red, map_smul, ic_zsmul, Int.cast_mul, smul_eq_mul]

noncomputable def redL (F : Type*) [CommRing F] (W : Submodule ℂ MF) : latt W →ₗ[ℤ] PowerSeries F where
  toFun := red F
  map_add' := red_add F
  map_smul' z v := by rw [red_zsmul, RingHom.id_apply, Int.cast_smul_eq_zsmul]

theorem redL_apply (F : Type*) [CommRing F] {W : Submodule ℂ MF} (v : latt W) : redL F W v = red F v := rfl

theorem linearIndependent_red_zmod {W : Submodule ℂ MF} (p : ℕ) (hp : p = 0 ∨ p.Prime)
    {J : Type*} [Fintype J] (b : Module.Basis J ℤ (latt W)) :
    LinearIndependent (ZMod p) (fun j => red (ZMod p) (b j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j₀

  choose ct hct using fun j => ZMod.intCast_surjective (c j)
  set v : latt W := ∑ j, ct j • b j with hv
  have hred : red (ZMod p) v = 0 := by
    rw [← redL_apply, hv, map_sum]
    simp only [map_smul, redL_apply]
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hct j, Int.cast_smul_eq_zsmul]
  have hdiv : ∀ n, (p : ℤ) ∣ ic v n := fun n => by
    have := congrArg (PowerSeries.coeff n) hred
    rw [coeff_red, map_zero] at this
    exact (CharP.intCast_eq_zero_iff (ZMod p) p _).mp this

  obtain ⟨w, hw⟩ : ∃ w : latt W, v = (p : ℤ) • w := by
    rcases hp with rfl | hp
    · refine ⟨0, ?_⟩
      rw [Nat.cast_zero, zero_smul]
      apply Subtype.ext
      refine eq_zero_of_forall_qCoeff (v : MF) fun n => ?_
      rw [ic_spec, show ic v n = 0 from zero_dvd_iff.mp (by simpa using hdiv n), Int.cast_zero]
    · exact latt_saturated v p (Int.natCast_ne_zero.mpr hp.ne_zero) hdiv

  have hcoord : ct j₀ = (p : ℤ) * b.repr w j₀ := by
    have h1 : b.repr v j₀ = ct j₀ := by
      rw [hv, map_sum]
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finset.sum_apply',
        Finsupp.single_apply]
      rw [Finset.sum_eq_single j₀ (fun j _ hj => if_neg hj) (fun h => absurd (Finset.mem_univ j₀) h), if_pos rfl]
    rw [← h1, hw, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [← hct j₀, hcoord, Int.cast_mul, (CharP.intCast_eq_zero_iff (ZMod p) p _).mpr (dvd_refl _), zero_mul]

theorem linearIndependent_red (F : Type) [Field F] {W : Submodule ℂ MF}
    {J : Type*} [Fintype J] (b : Module.Basis J ℤ (latt W)) :
    LinearIndependent F (fun j => red F (b j)) := by
  classical

  let p := ringChar F
  haveI hchar : CharP F p := ringChar.charP F
  have hp : p = 0 ∨ p.Prime := (CharP.char_is_prime_or_zero F p).symm
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  haveI : FaithfulSMul (ZMod p) F :=
    (faithfulSMul_iff_algebraMap_injective (ZMod p) F).mpr (ZMod.castHom_injective F)
  have halg : ∀ z : ℤ, algebraMap (ZMod p) F (z : ZMod p) = (z : F) := fun z => map_intCast _ z

  let S : Submodule F (PowerSeries F) := Submodule.span F (Set.range fun j => red F (b j))
  haveI : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range _)
  obtain ⟨n₁, hn₁⟩ := exists_window (L := F) (V := S) (fun n => (PowerSeries.coeff n).comp S.subtype)
    (fun x hx => Subtype.ext (PowerSeries.ext fun n => by simpa using hx n))

  let tR : J → Fin n₁ → ZMod p := fun j m => (ic (b j) m : ZMod p)
  have htR : LinearIndependent (ZMod p) tR := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hfull := linearIndependent_red_zmod p hp b
    rw [Fintype.linearIndependent_iff] at hfull
    refine hfull c ?_

    set x : PowerSeries (ZMod p) := ∑ j, c j • red (ZMod p) (b j) with hx
    let y : PowerSeries F := ∑ j, algebraMap (ZMod p) F (c j) • red F (b j)
    have hyS : y ∈ S := S.sum_mem fun j _ => S.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    have hxy : ∀ n, algebraMap (ZMod p) F (PowerSeries.coeff n x) = PowerSeries.coeff n y := fun n => by
      simp only [hx, y, map_sum, map_smul, coeff_red, smul_eq_mul, map_mul, halg]
    have hy0 : y = 0 := by
      have := hn₁ ⟨y, hyS⟩ fun m hm => by
        change PowerSeries.coeff m y = 0
        rw [← hxy m]
        have hcm := congrFun hc ⟨m, hm⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tR] at hcm
        have : PowerSeries.coeff m x = 0 := by
          simp only [hx, map_sum, map_smul, coeff_red, smul_eq_mul]; exact hcm
        rw [this, map_zero]
      exact congrArg Subtype.val this
    ext n
    apply (ZMod.castHom_injective F)
    change algebraMap (ZMod p) F (PowerSeries.coeff n x) = algebraMap (ZMod p) F (PowerSeries.coeff n 0)
    simp only [hxy n, hy0, map_zero]

  have htF : LinearIndependent F (fun j => algebraMap (ZMod p) F ∘ tR j) :=
    linearIndependent_algebraMap_comp_iff.mpr htR

  let trunc : PowerSeries F →ₗ[F] (Fin n₁ → F) :=
    { toFun := fun φ m => PowerSeries.coeff m φ
      map_add' := fun φ ψ => funext fun m => map_add _ _ _
      map_smul' := fun a φ => funext fun m => by simp }
  have hcomp : trunc ∘ (fun j => red F (b j)) = fun j => algebraMap (ZMod p) F ∘ tR j := by
    funext j; funext m
    simp only [Function.comp_apply, trunc, LinearMap.coe_mk, AddHom.coe_mk, coeff_red, tR, halg]
  exact LinearIndependent.of_comp trunc (hcomp ▸ htF)

end Reduction
p2m_reactivate "P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.RedRankCusp"

end RedRankCusp
p2m_reactivate "P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.RedRankCusp"

namespace RedRankCusp

section Main

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)
local notation "MF" => CuspForm Γ₀(N) k

theorem red_mem_modPCusp (F : Type) [Field F] {W : Submodule ℂ MF} (v : latt W) :
    red F v ∈ ModPForms.modPCusp N k F :=
  Submodule.subset_span ⟨(v : MF), ic v, fun n => ic_spec v n, rfl⟩

theorem red_mem_span (F : Type) [Field F] {W : Submodule ℂ MF} {J : Type*} [Fintype J]
    (b : Module.Basis J ℤ (latt W)) (v : latt W) :
    red F v ∈ Submodule.span F (Set.range fun j => red F (b j)) := by
  classical
  have hv : v = ∑ j, b.repr v j • b j := (b.sum_repr v).symm
  rw [hv, ← redL_apply, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul, redL_apply, ← Int.cast_smul_eq_zsmul F]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

variable (N k)

theorem finiteDimensional_cuspForm [NeZero N] : FiniteDimensional ℂ MF := by
  haveI : FiniteDimensional ℂ (ModularForm Γ₀(N) k) :=
    (ModularForm.finiteDimensional_and_finrank_le_of_isArithmetic Γ₀(N) k (hΓ N)).1
  exact Module.Finite.of_injective (CuspForm.toModularFormₗ : MF →ₗ[ℂ] ModularForm Γ₀(N) k)
    CuspForm.toModularFormₗ_injective

theorem modPCusp_finite [NeZero N] (F : Type) [Field F] : Module.Finite F ↥(ModPForms.modPCusp N k F) := by
  classical
  haveI : FiniteDimensional ℂ MF := finiteDimensional_cuspForm N k
  obtain ⟨hfin, hfree⟩ := latt_finite_free (N := N) (k := k) (⊤ : Submodule ℂ MF)
  haveI := hfin; haveI := hfree
  let b := Module.Free.chooseBasis ℤ (latt (⊤ : Submodule ℂ MF))
  let S : Submodule F (PowerSeries F) := Submodule.span F (Set.range fun j => red F (b j))
  haveI : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range _)
  have hle : ModPForms.modPCusp N k F ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro φ ⟨g, a, hga, rfl⟩
    let v : latt (⊤ : Submodule ℂ MF) := ⟨g, Submodule.mem_top, fun n => ⟨a n, hga n⟩⟩
    have : (PowerSeries.mk fun n => ((a n : ℤ) : F)) = red F v := by
      ext n
      rw [PowerSeries.coeff_mk, coeff_red, ic_eq_of_qCoeff_eq v n (a n) (hga n)]
    rw [this]
    exact red_mem_span F b v
  exact Submodule.finiteDimensional_of_le hle

theorem card_le_finrank [NeZero N] (F : Type) [Field F] {ι : Type} [Fintype ι]
    (f : ι → MF) (a : ι → ℕ → ℤ)
    (hf : ∀ i n, ModularFormClass.qCoeff (f i) n = (a i n : ℂ))
    (hli : LinearIndependent ℂ f) :
    Fintype.card ι ≤ Module.finrank F ↥(ModPForms.modPCusp N k F) := by
  classical
  haveI : FiniteDimensional ℂ MF := finiteDimensional_cuspForm N k
  let W : Submodule ℂ MF := Submodule.span ℂ (Set.range f)
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  obtain ⟨hfin, hfree⟩ := latt_finite_free (N := N) (k := k) W
  haveI := hfin; haveI := hfree
  let b := Module.Free.chooseBasis ℤ (latt W)
  have h1 : Fintype.card ι ≤ Module.finrank ℤ (latt W) := by
    let fι : ι → latt W := fun i => ⟨f i, Submodule.subset_span ⟨i, rfl⟩, fun n => ⟨a i n, hf i n⟩⟩
    have hind : LinearIndependent ℤ fι := by
      apply LinearIndependent.of_comp (latt W).subtype
      exact hli.restrict_scalars' ℤ
    exact hind.fintype_card_le_finrank
  have h2 : Module.finrank ℤ (latt W) ≤ Module.finrank F ↥(ModPForms.modPCusp N k F) := by
    rw [Module.finrank_eq_card_chooseBasisIndex]
    haveI := modPCusp_finite N k F
    let g : Module.Free.ChooseBasisIndex ℤ (latt W) → ↥(ModPForms.modPCusp N k F) :=
      fun j => ⟨red F (b j), red_mem_modPCusp F (b j)⟩
    have hind : LinearIndependent F g :=
      LinearIndependent.of_comp (ModPForms.modPCusp N k F).subtype (linearIndependent_red F b)
    exact hind.fintype_card_le_finrank
  exact h1.trans h2

end Main
p2m_reactivate "P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.RedRankCusp"

end RedRankCusp
p2m_reactivate "P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.RedRankCusp"

theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) (F : Type) [Field F] {ι : Type} [Fintype ι]
    (f : ι → CuspForm (CongruenceSubgroup.Gamma0 N) k) (a : ι → ℕ → ℤ)
    (hf : ∀ i n, ModularFormClass.qCoeff (f i) n = (a i n : ℂ))
    (hli : LinearIndependent ℂ f) :
    Fintype.card ι ≤ Module.finrank F ↥(ModPForms.modPCusp N k F) :=
  RedRankCusp.card_le_finrank N k F f a hf hli

end S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent
end P2MW
export P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent (solution)
