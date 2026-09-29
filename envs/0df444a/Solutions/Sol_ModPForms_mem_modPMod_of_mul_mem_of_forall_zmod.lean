-- Prove2me | solution 1 for ModPForms.mem_modPMod_of_mul_mem_of_forall_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a3fbbc14-eb58-51fd-8827-1afbd0ebb56c

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_mem_modPMod_of_mul_mem_of_forall_zmod
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace ModPForms
p2m_export "ModPForms" "modPCusp modPMod"
namespace BaseChange
p2m_open "ModPForms"

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p]

noncomputable abbrev ι : PowerSeries (ZMod p) →+* PowerSeries F :=
  PowerSeries.map (ZMod.castHom (dvd_refl p) F)

theorem ι_mk_intCast (a : ℕ → ℤ) :
    ι p F (PowerSeries.mk fun n => ((a n : ℤ) : ZMod p)) = PowerSeries.mk fun n => ((a n : ℤ) : F) := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_intCast]

theorem span_image_span (S : Set (PowerSeries (ZMod p))) :
    Submodule.span F (ι p F '' (Submodule.span (ZMod p) S : Set (PowerSeries (ZMod p)))) =
      Submodule.span F (ι p F '' S) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      have : ι p F (c • y) = (ZMod.castHom (dvd_refl p) F c) • ι p F y := by
        rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, ← PowerSeries.smul_eq_C_mul]
      rw [this]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem genSet_modPMod_eq_image (N : ℕ) (k : ℤ) :
    {φ : PowerSeries F | ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)} =
    ι p F '' {φ : PowerSeries (ZMod p) | ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : ZMod p)} := by
  ext φ
  constructor
  · rintro ⟨f, a, ha, rfl⟩
    exact ⟨_, ⟨f, a, ha, rfl⟩, ι_mk_intCast p F a⟩
  · rintro ⟨_, ⟨f, a, ha, rfl⟩, rfl⟩
    exact ⟨f, a, ha, ι_mk_intCast p F a⟩

theorem genSet_modPCusp_eq_image (N : ℕ) (k : ℤ) :
    {φ : PowerSeries F | ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)} =
    ι p F '' {φ : PowerSeries (ZMod p) | ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : ZMod p)} := by
  ext φ
  constructor
  · rintro ⟨f, a, ha, rfl⟩
    exact ⟨_, ⟨f, a, ha, rfl⟩, ι_mk_intCast p F a⟩
  · rintro ⟨_, ⟨f, a, ha, rfl⟩, rfl⟩
    exact ⟨f, a, ha, ι_mk_intCast p F a⟩

theorem modPMod_eq_span_image (N : ℕ) (k : ℤ) :
    ModPForms.modPMod N k F =
      Submodule.span F (ι p F '' (ModPForms.modPMod N k (ZMod p) : Set (PowerSeries (ZMod p)))) := by
  rw [ModPForms.modPMod, ModPForms.modPMod, span_image_span, genSet_modPMod_eq_image]

theorem modPCusp_eq_span_image (N : ℕ) (k : ℤ) :
    ModPForms.modPCusp N k F =
      Submodule.span F (ι p F '' (ModPForms.modPCusp N k (ZMod p) : Set (PowerSeries (ZMod p)))) := by
  rw [ModPForms.modPCusp, ModPForms.modPCusp, span_image_span, genSet_modPCusp_eq_image]

theorem modPMod_le_modPMod_of_zmod (N : ℕ) (k : ℤ) (N' : ℕ) (k' : ℤ)
    (h : ModPForms.modPMod N k (ZMod p) ≤ ModPForms.modPMod N' k' (ZMod p)) :
    ModPForms.modPMod N k F ≤ ModPForms.modPMod N' k' F := by
  rw [modPMod_eq_span_image p F N k, modPMod_eq_span_image p F N' k']
  exact Submodule.span_mono (Set.image_mono h)

theorem modPCusp_le_modPCusp_of_zmod (N : ℕ) (k : ℤ) (N' : ℕ) (k' : ℤ)
    (h : ModPForms.modPCusp N k (ZMod p) ≤ ModPForms.modPCusp N' k' (ZMod p)) :
    ModPForms.modPCusp N k F ≤ ModPForms.modPCusp N' k' F := by
  rw [modPCusp_eq_span_image p F N k, modPCusp_eq_span_image p F N' k']
  exact Submodule.span_mono (Set.image_mono h)

section Coordinates
variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p]

noncomputable def coordPS (lam : F →+ ZMod p) : PowerSeries F →+ PowerSeries (ZMod p) where
  toFun φ := PowerSeries.mk fun n => lam (PowerSeries.coeff n φ)
  map_zero' := by ext n; simp
  map_add' φ ψ := by ext n; simp

theorem coeff_coordPS (lam : F →+ ZMod p) (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (coordPS p F lam φ) = lam (PowerSeries.coeff n φ) := by
  simp [coordPS, PowerSeries.coeff_mk]

theorem coordPS_smul_ι (lam : F →+ ZMod p)
    (hlam : ∀ (t : ZMod p) (c : F), lam ((ZMod.castHom (dvd_refl p) F t) * c) = t * lam c)
    (c : F) (s : PowerSeries (ZMod p)) :
    coordPS p F lam (c • ι p F s) = lam c • s := by
  ext n
  rw [coeff_coordPS, PowerSeries.coeff_smul, PowerSeries.coeff_smul, PowerSeries.coeff_map, smul_eq_mul,
    smul_eq_mul, mul_comm c, hlam, mul_comm]

theorem coordPS_mem_of_mem_span_image (lam : F →+ ZMod p)
    (hlam : ∀ (t : ZMod p) (c : F), lam ((ZMod.castHom (dvd_refl p) F t) * c) = t * lam c)
    (S : Submodule (ZMod p) (PowerSeries (ZMod p))) (φ : PowerSeries F)
    (hφ : φ ∈ Submodule.span F (ι p F '' (S : Set (PowerSeries (ZMod p))))) :
    coordPS p F lam φ ∈ S := by
  suffices h : ∀ c : F, coordPS p F lam (c • φ) ∈ S by simpa using h 1
  induction hφ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, hs, rfl⟩ := hy
    intro c
    rw [coordPS_smul_ι p F lam hlam]
    exact S.smul_mem _ hs
  | zero => intro c; rw [smul_zero, map_zero]; exact S.zero_mem
  | add y z _ _ hy hz => intro c; rw [smul_add, map_add]; exact S.add_mem (hy c) (hz c)
  | smul c' y _ hy => intro c; rw [smul_smul]; exact hy (c * c')

theorem eq_zero_of_forall_coordPS_eq_zero {B : Type} (lam : B → (F →+ ZMod p))
    (hdet : ∀ c : F, (∀ b, lam b c = 0) → c = 0) (φ : PowerSeries F)
    (h : ∀ b, coordPS p F (lam b) φ = 0) : φ = 0 := by
  ext n
  rw [map_zero]
  refine hdet _ fun b => ?_
  have := congrArg (PowerSeries.coeff n) (h b)
  rwa [coeff_coordPS, map_zero] at this

theorem exists_coord_family :
    ∃ (B : Type) (lam : B → (F →+ ZMod p)),
      (∀ b (t : ZMod p) (c : F), lam b ((ZMod.castHom (dvd_refl p) F t) * c) = t * lam b c) ∧
      (∀ c : F, (∀ b, lam b c = 0) → c = 0) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let bs := Module.Free.chooseBasis (ZMod p) F
  refine ⟨Module.Free.ChooseBasisIndex (ZMod p) F, fun b => (bs.coord b).toAddMonoidHom, ?_, ?_⟩
  · intro b t c
    show bs.coord b (algebraMap (ZMod p) F t * c) = t * bs.coord b c
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro c hc
    exact bs.forall_coord_eq_zero_iff.mp hc

end Coordinates

section Transfer
variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p]

theorem forall_eq_zero_of_sum_eq_zero_of_forall_zmod (N : ℕ) {r : ℕ} (κ : Fin r → ℤ)
    (h : ∀ ψ : Fin r → PowerSeries (ZMod p),
      (∀ a, ψ a ∈ ModPForms.modPMod N (κ a) (ZMod p)) → ∑ a, ψ a = 0 → ∀ a, ψ a = 0)
    (φ : Fin r → PowerSeries F) (hφ : ∀ a, φ a ∈ ModPForms.modPMod N (κ a) F) (hsum : ∑ a, φ a = 0) :
    ∀ a, φ a = 0 := by
  obtain ⟨B, lam, hlam, hdet⟩ := exists_coord_family p F
  intro a
  refine eq_zero_of_forall_coordPS_eq_zero p F lam hdet (φ a) fun b => ?_
  refine h (fun a' => coordPS p F (lam b) (φ a')) (fun a' => ?_) ?_ a
  · refine coordPS_mem_of_mem_span_image p F (lam b) (hlam b) _ (φ a') ?_
    rw [← modPMod_eq_span_image p F N (κ a')]
    exact hφ a'
  · rw [← map_sum, hsum, map_zero]

end Transfer

section Reconstruct
variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p]

theorem ι_smul (t : ZMod p) (s : PowerSeries (ZMod p)) :
    ι p F (t • s) = (ZMod.castHom (dvd_refl p) F t) • ι p F s := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, ← PowerSeries.smul_eq_C_mul]

theorem mem_span_image_of_forall_coordPS_mem (T : Submodule (ZMod p) (PowerSeries (ZMod p)))
    (φ : PowerSeries F) (hfin : φ ∈ Submodule.span F (Set.range (ι p F)))
    (hT : letI : Algebra (ZMod p) F := ZMod.algebra F p
      ∀ b, coordPS p F ((Module.Free.chooseBasis (ZMod p) F).coord b).toAddMonoidHom φ ∈ T) :
    φ ∈ Submodule.span F (ι p F '' (T : Set (PowerSeries (ZMod p)))) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  set bs := Module.Free.chooseBasis (ZMod p) F with hbs

  set lam : Module.Free.ChooseBasisIndex (ZMod p) F → (F →+ ZMod p) := fun b => (bs.coord b).toAddMonoidHom
    with hlamdef
  have hlam_apply : ∀ b (c : F), lam b c = bs.repr c b := fun b c => rfl
  have halg : ∀ t : ZMod p, algebraMap (ZMod p) F t = ZMod.castHom (dvd_refl p) F t := fun t => rfl
  have hlam : ∀ b (t : ZMod p) (c : F), lam b ((ZMod.castHom (dvd_refl p) F t) * c) = t * lam b c := by
    intro b t c
    rw [hlam_apply, hlam_apply, ← halg, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

  have R0 : ∀ (ψ : PowerSeries F) (B₀ : Finset (Module.Free.ChooseBasisIndex (ZMod p) F)),
      (∀ b, b ∉ B₀ → coordPS p F (lam b) ψ = 0) →
      ψ = ∑ b ∈ B₀, bs b • ι p F (coordPS p F (lam b) ψ) := by
    intro ψ B₀ hB
    ext n
    rw [map_sum]
    simp only [PowerSeries.coeff_smul, PowerSeries.coeff_map, coeff_coordPS, smul_eq_mul]
    have hsub : (bs.repr (PowerSeries.coeff n ψ)).support ⊆ B₀ := by
      intro b hb
      by_contra hbB
      have h0 := congrArg (PowerSeries.coeff n) (hB b hbB)
      rw [coeff_coordPS, map_zero, hlam_apply] at h0
      exact (Finsupp.mem_support_iff.mp hb) h0
    conv_lhs => rw [← bs.linearCombination_repr (PowerSeries.coeff n ψ), Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hsub (fun i a => a • bs i) (fun i _ => zero_smul _ _)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Algebra.smul_def, halg, hlam_apply, mul_comm]

  have R1 : ∀ φ' : PowerSeries F, φ' ∈ Submodule.span F (Set.range (ι p F)) →
      ∃ B₀ : Finset (Module.Free.ChooseBasisIndex (ZMod p) F),
      ∀ b, b ∉ B₀ → coordPS p F (lam b) φ' = 0 := by
    intro φ' hφ'
    induction hφ' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      refine ⟨(bs.repr 1).support, fun b hb => ?_⟩
      have : ι p F s = (1 : F) • ι p F s := (one_smul _ _).symm
      rw [this, coordPS_smul_ι p F (lam b) (hlam b), hlam_apply]
      have h0 : bs.repr 1 b = 0 := by
        by_contra h; exact hb (Finsupp.mem_support_iff.mpr h)
      rw [h0, zero_smul]
    | zero => exact ⟨∅, fun b _ => map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨B₁, h₁⟩ := hy
      obtain ⟨B₂, h₂⟩ := hz
      classical
      refine ⟨B₁ ∪ B₂, fun b hb => ?_⟩
      rw [Finset.mem_union, not_or] at hb
      rw [map_add, h₁ b hb.1, h₂ b hb.2, add_zero]
    | smul c y _ hy =>
      obtain ⟨B₀, h₀⟩ := hy
      classical
      refine ⟨B₀.biUnion fun b' => (bs.repr (c * bs b')).support, fun b hb => ?_⟩
      rw [R0 y B₀ h₀, Finset.smul_sum, map_sum]
      refine Finset.sum_eq_zero fun b' hb' => ?_
      rw [smul_smul, coordPS_smul_ι p F (lam b) (hlam b), hlam_apply]
      have h0 : bs.repr (c * bs b') b = 0 := by
        by_contra h
        exact hb (Finset.mem_biUnion.mpr ⟨b', hb', Finsupp.mem_support_iff.mpr h⟩)
      rw [h0, zero_smul]
  obtain ⟨B₀, h₀⟩ := R1 φ hfin
  rw [R0 φ B₀ h₀]
  refine Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hT b, rfl⟩)

theorem mem_of_mul_mem_of_forall_zmod' (N : ℕ) (k k' k'' : ℤ) (P : PowerSeries (ZMod p))
    (h : ∀ ψ : PowerSeries (ZMod p), ψ ∈ ModPForms.modPMod N k (ZMod p) →
      P * ψ ∈ ModPForms.modPMod N k' (ZMod p) → ψ ∈ ModPForms.modPMod N k'' (ZMod p))
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N k F)
    (hP : ι p F P * φ ∈ ModPForms.modPMod N k' F) :
    φ ∈ ModPForms.modPMod N k'' F := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  set bs := Module.Free.chooseBasis (ZMod p) F with hbs
  set lam : Module.Free.ChooseBasisIndex (ZMod p) F → (F →+ ZMod p) := fun b => (bs.coord b).toAddMonoidHom
    with hlamdef
  have hlam_apply : ∀ b (c : F), lam b c = bs.repr c b := fun b c => rfl
  have halg : ∀ t : ZMod p, algebraMap (ZMod p) F t = ZMod.castHom (dvd_refl p) F t := fun t => rfl
  have hlam : ∀ b (t : ZMod p) (c : F), lam b ((ZMod.castHom (dvd_refl p) F t) * c) = t * lam b c := by
    intro b t c
    rw [hlam_apply, hlam_apply, ← halg, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hmul : ∀ b, coordPS p F (lam b) (ι p F P * φ) = P * coordPS p F (lam b) φ := by
    intro b; ext n
    rw [coeff_coordPS, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [PowerSeries.coeff_map, hlam, coeff_coordPS]
  have hcoord : ∀ b, coordPS p F (lam b) φ ∈ ModPForms.modPMod N k'' (ZMod p) := by
    intro b
    refine h _ ?_ ?_
    · exact coordPS_mem_of_mem_span_image p F (lam b) (hlam b) _ φ
        (by rw [← modPMod_eq_span_image p F N k]; exact hφ)
    · rw [← hmul]
      exact coordPS_mem_of_mem_span_image p F (lam b) (hlam b) _ _
        (by rw [← modPMod_eq_span_image p F N k']; exact hP)
  rw [modPMod_eq_span_image p F N k'']
  refine mem_span_image_of_forall_coordPS_mem p F _ φ ?_ hcoord
  rw [modPMod_eq_span_image p F N k] at hφ
  exact Submodule.span_mono (Set.image_subset_range _ _) hφ

end Reconstruct

end ModPForms.BaseChange

theorem solution (p : ℕ) [Fact p.Prime] (N : ℕ) (k k' k'' : ℤ) (F : Type) [Field F] [CharP F p]
    (P : PowerSeries (ZMod p))
    (h : ∀ ψ : PowerSeries (ZMod p), ψ ∈ ModPForms.modPMod N k (ZMod p) →
      P * ψ ∈ ModPForms.modPMod N k' (ZMod p) → ψ ∈ ModPForms.modPMod N k'' (ZMod p))
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N k F)
    (hP : PowerSeries.map (ZMod.castHom (dvd_refl p) F) P * φ ∈ ModPForms.modPMod N k' F) :
    φ ∈ ModPForms.modPMod N k'' F :=
  ModPForms.BaseChange.mem_of_mul_mem_of_forall_zmod' p F N k k' k'' P h φ hφ hP

end S_ModPForms_mem_modPMod_of_mul_mem_of_forall_zmod
end P2MW
export P2MW.S_ModPForms_mem_modPMod_of_mul_mem_of_forall_zmod (solution)
