-- Prove2me | solution 1 for ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/676059b3-a831-5be5-9ee2-677a76780329

import Mathlib
import Definitions.Def_ModularCurve_AbelFibreSumOf
import Theorems.Thm_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero_of_finiteIndex
import Theorems.Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
import Theorems.Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole
import Theorems.Thm_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub
import Theorems.Thm_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos
import Theorems.Thm_UpperHalfPlane_exists_residue_cuspForm_div_sub
import Theorems.Thm_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt
import Theorems.Thm_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf

noncomputable section

open UpperHalfPlane Filter Complex MulAction
open scoped MatrixGroups Topology ModularForm Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "orbifoldIndexOf abelFibreSumOf orbifoldIndexOf_def abelFibreSumOf_def periodAlongOf periodOf periodLatticeOf periodOf_mem_periodLatticeOf period valueMultiplicity abelFibreSum valueMultiplicity_of_eq_coe periodAlongOf_smul_sub_periodAlongOf_eq_periodOf exists_hasEquivariantPrimitiveOf finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero_of_finiteIndex periodAlongOf_apply_eq_sub_of_hasDerivAt"
namespace FibreConstOf
namespace Bridge
p2m_open "ModularCurve"

variable {Γ : Subgroup SL(2, ℤ)}

theorem negOne_mem_sup : (-1 : SL(2, ℤ)) ∈ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem mem_sup_of_mem {g : SL(2, ℤ)} (hg : g ∈ Γ) : g ∈ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) :=
  Subgroup.mem_sup_left hg

theorem negOne_smul (z : ℍ) : (-1 : SL(2, ℤ)) • z = z := by
  ext1
  simp

theorem neg_smul_eq (g : SL(2, ℤ)) (z : ℍ) : (-g) • z = g • z := by
  rw [← neg_one_mul, mul_smul, negOne_smul]

theorem exists_mem_smul_eq {g : SL(2, ℤ)} (hg : g ∈ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) :
    ∃ γ ∈ Γ, ∀ z : ℍ, g • z = γ • z := by
  rcases (Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff Γ g).mp hg with h | h
  · exact ⟨g, h, fun _ => rfl⟩
  · refine ⟨-g, h, fun z => ?_⟩
    rw [neg_smul_eq]

theorem forall_mem_sup {X : Sort*} {u : ℍ → X} (hu : ∀ γ ∈ Γ, ∀ z : ℍ, u (γ • z) = u z) :
    ∀ g ∈ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)), ∀ z : ℍ, u (g • z) = u z := by
  intro g hg z
  obtain ⟨γ, hγ, hγz⟩ := exists_mem_smul_eq hg
  rw [hγz z, hu γ hγ z]

theorem exists_mem_smul_eq_of_sup {x y : ℍ} (h : ∃ g ∈ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)), g • x = y) :
    ∃ γ ∈ Γ, γ • x = y := by
  obtain ⟨g, hg, hgx⟩ := h
  obtain ⟨γ, hγ, hγz⟩ := exists_mem_smul_eq hg
  exact ⟨γ, hγ, by rw [← hγz, hgx]⟩

theorem mem_zpowers_negOne_iff (x : SL(2, ℤ)) :
    x ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ x = 1 ∨ x = -1 := by
  have h := Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff ⊥ x
  rw [bot_sup_eq] at h
  rw [h, Subgroup.mem_bot, Subgroup.mem_bot, neg_eq_iff_eq_neg]

theorem finite_setOf_smul_eq (τ : ℍ) : {g : SL(2, ℤ) | g • τ = τ}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_stabilizer' (↥𝒮ℒ) τ
  let φ : SL(2, ℤ) → ↥𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa [φ] using this
  have hset : {g : SL(2, ℤ) | g • τ = τ} = φ ⁻¹' {s : ↥𝒮ℒ | s • τ = τ} := by
    ext g
    rfl
  rw [hset]
  exact h.preimage hφ.injOn

scoped instance finite_stabilizer (Γ₁ : Subgroup SL(2, ℤ)) (τ : ℍ) :
    Finite (MulAction.stabilizer Γ₁ τ) := by
  have h := (finite_setOf_smul_eq τ).preimage (Subtype.val_injective (p := (· ∈ Γ₁))).injOn
  exact Set.finite_coe_iff.mpr (h.subset fun γ hγ => hγ)

theorem two_le_card_stabilizer_sup (τ : ℍ) :
    2 ≤ Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) := by
  have h1 : (1 : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) ∈ MulAction.stabilizer _ τ := one_mem _
  have h2 : (⟨-1, negOne_mem_sup⟩ : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) ∈
      MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ := by
    show ((-1 : SL(2, ℤ))) • τ = τ
    exact negOne_smul τ
  have hne : (⟨1, h1⟩ : MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) ≠ ⟨_, h2⟩ := by
    intro h
    have h' := congrArg (fun x => ((x.1 : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) : SL(2, ℤ)) 0 0) h
    simp at h'
  have : 1 < Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) :=
    Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hne⟩⟩
  omega

theorem orbifoldIndexOf_pos (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : 0 < ModularCurve.orbifoldIndexOf Γ τ := by
  rw [ModularCurve.orbifoldIndexOf_def]
  exact Nat.div_pos (two_le_card_stabilizer_sup τ) two_pos

variable {F : ℍ → ℂ}

theorem card_stabilizer_sup_eq_two
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) {t : ℂ} {r : ℍ}
    (h1 : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (r : ℂ) = 1) :
    Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) r) = 2 := by
  have hΓ' := forall_mem_sup (u := F) hΓ
  have hdvd := UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
    (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) (fun w => F w - t)
    (fun γ hγ τ => by simp only [hΓ' γ hγ τ]) r 1
    (show meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (r : ℂ) = ((1 : ℤ) : WithTop ℤ)
      from h1)
  rw [mul_one] at hdvd
  have hle : Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) r) ≤ 2 :=
    Nat.le_of_dvd two_pos (by exact_mod_cast hdvd)
  have := two_le_card_stabilizer_sup (Γ := Γ) r
  omega

theorem eq_one_or_eq_negOne_of_smul_eq
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) {t : ℂ} {r : ℍ}
    (h1 : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (r : ℂ) = 1)
    {g : SL(2, ℤ)} (hg : g ∈ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) (hgr : g • r = r) :
    g = 1 ∨ g = -1 := by
  by_contra hcon
  push Not at hcon
  have hcard := card_stabilizer_sup_eq_two hΓ h1

  let e : Fin 3 → MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) r :=
    ![⟨1, one_mem _⟩, ⟨⟨-1, negOne_mem_sup⟩, show ((-1 : SL(2, ℤ))) • r = r from negOne_smul r⟩,
      ⟨⟨g, hg⟩, show g • r = r from hgr⟩]
  have hinj : Function.Injective e := by
    have h01 : (1 : SL(2, ℤ)) ≠ -1 := by
      intro h
      have h' := congrArg (fun x : SL(2, ℤ) => x 0 0) h
      simp at h'
    intro i j hij
    have hv : ((e i).1 : SL(2, ℤ)) = ((e j).1 : SL(2, ℤ)) := by rw [hij]
    fin_cases i <;> fin_cases j <;>
      simp [e, h01, h01.symm, hcon.1, hcon.2, Ne.symm hcon.1, Ne.symm hcon.2] at hv ⊢
  have h3 : 3 ≤ Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) r) := by
    simpa using Nat.card_le_card_of_injective e hinj
  omega

theorem natCard_stabilizer_eq_k
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) {t : ℂ} {r : ℍ}
    (h1 : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (r : ℂ) = 1) :
    Nat.card (MulAction.stabilizer Γ r) =
      Nat.card (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨((x.1 : Γ) : SL(2, ℤ)), (x.1 : Γ).2, ?_⟩
      invFun := fun y => ⟨⟨(y : SL(2, ℤ)), (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl }
  ·
    have hx : ((x.1 : Γ) : SL(2, ℤ)) • r = r := x.2
    rcases eq_one_or_eq_negOne_of_smul_eq hΓ h1 (mem_sup_of_mem (x.1 : Γ).2) hx with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  ·
    show ((y : SL(2, ℤ))) • r = r
    rcases (mem_zpowers_negOne_iff _).mp (Subgroup.mem_inf.mp y.2).2 with h | h
    · rw [h, one_smul]
    · rw [h, negOne_smul]

theorem k_pos : 0 < Nat.card (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) := by
  have hfin : Finite (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) := by
    have hsub : ((Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) ⊆
        {1, -1} := by
      intro x hx
      rcases (mem_zpowers_negOne_iff x).mp (Subgroup.mem_inf.mp hx).2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact Set.Finite.to_subtype ((Set.toFinite {1, -1}).subset hsub)
  haveI := hfin
  exact Nat.card_pos

end ModularCurve.FibreConstOf.Bridge
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf"
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

namespace ModularCurve
p2m_export "ModularCurve" "orbifoldIndexOf abelFibreSumOf orbifoldIndexOf_def abelFibreSumOf_def periodAlongOf periodOf periodLatticeOf periodOf_mem_periodLatticeOf period valueMultiplicity abelFibreSum valueMultiplicity_of_eq_coe periodAlongOf_smul_sub_periodAlongOf_eq_periodOf exists_hasEquivariantPrimitiveOf finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero_of_finiteIndex periodAlongOf_apply_eq_sub_of_hasDerivAt"
namespace FibreConstOf
p2m_open "ModularCurve"

open ModularCurve.FibreConstOf.Bridge

variable {Γ : Subgroup SL(2, ℤ)}

local notation "Γ′" => (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem tendsto_coe_nhdsNE (τ : ℍ) :
    Tendsto ((↑) : ℍ → ℂ) (𝓝[≠] τ) (𝓝[≠] (τ : ℂ)) :=
  (map_coe_nhdsNE τ).le

theorem det_pos (g : SL(2, ℤ)) : 0 < ((g : GL (Fin 2) ℝ)).val.det := by
  have h : ((g : GL (Fin 2) ℝ)).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  rw [h]; exact one_pos

theorem smul_eq_coe_smul (g : SL(2, ℤ)) (z : ℍ) : g • z = (g : SL(2, ℝ)) • z := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • z =
    (Matrix.SpecialLinearGroup.mapGL ℝ (g : SL(2, ℝ))) • z
  congr 1

theorem dist_smul_smul (g : SL(2, ℤ)) (x y : ℍ) : dist (g • x) (g • y) = dist x y := by
  rw [smul_eq_coe_smul, smul_eq_coe_smul]
  exact dist_smul _ _ _

def toSLsub (g : SL(2, ℤ)) : ↥𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict g

theorem toSLsub_smul (g : SL(2, ℤ)) (z : ℍ) : toSLsub g • z = g • z := rfl

section Orders

variable (F : ℍ → ℂ) (t : ℂ)

def fsub : ℂ → ℂ := fun z => F (ofComplex z) - t

def ord (τ : ℍ) : WithTop ℤ := meromorphicOrderAt (fsub F t) (τ : ℂ)

def U : Set ℂ := {z : ℂ | 0 < z.im}

def Φ : ℂ → ℂ := toMeromorphicNFOn (fun z : ℂ => F (ofComplex z)) U

variable {F t}

theorem ord_smul {G : Subgroup SL(2, ℤ)} (hG : ∀ γ ∈ G, ∀ τ : ℍ, F (γ • τ) = F τ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ G) (τ : ℍ) :
    ord F t (γ • τ) = ord F t τ := by
  unfold ord fsub
  rw [show (((γ • τ : ℍ)) : ℂ) = ↑(((γ : GL (Fin 2) ℝ)) • τ) by simp,
    ← meromorphicOrderAt_comp_smul (f := fun w : ℍ => F w - t) (det_pos γ)]
  congr 1
  funext z
  rw [show (((γ : GL (Fin 2) ℝ)) • ofComplex z) = γ • ofComplex z by simp]
  rw [hG γ hγ _]

theorem merAt_fsub (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (t : ℂ) (τ : ℍ) : MeromorphicAt (fsub F t) (τ : ℂ) :=
  (hF τ).sub (MeromorphicAt.const t _)

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_im

theorem coe_mem_U (τ : ℍ) : (τ : ℂ) ∈ U := τ.im_pos

theorem merOn (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) :
    MeromorphicOn (fun z : ℂ => F (ofComplex z)) U := fun z hz => hF ⟨z, hz⟩

theorem Φ_eventuallyEq (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (τ : ℍ) : Φ F =ᶠ[𝓝[≠] (τ : ℂ)] fun z => F (ofComplex z) :=
  (merOn hF).toMeromorphicNFOn_eq_self_on_nhdsNE (coe_mem_U τ)

theorem Φ_NF (F : ℍ → ℂ) (τ : ℍ) : MeromorphicNFAt (Φ F) (τ : ℂ) :=
  meromorphicNFOn_toMeromorphicNFOn _ U (coe_mem_U τ)

theorem Φ_merAt (F : ℍ → ℂ) (τ : ℍ) : MeromorphicAt (Φ F) (τ : ℂ) := (Φ_NF F τ).meromorphicAt

theorem ord_Φ (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (t : ℂ) (τ : ℍ) : meromorphicOrderAt (fun z => Φ F z - t) (τ : ℂ) = ord F t τ := by
  apply meromorphicOrderAt_congr
  filter_upwards [Φ_eventuallyEq hF τ] with z hz
  simp [fsub, hz]

theorem Φ_analyticAt (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    {t : ℂ} {τ : ℍ} (h : 0 ≤ ord F t τ) : AnalyticAt ℂ (Φ F) (τ : ℂ) := by
  rw [← (Φ_NF F τ).meromorphicOrderAt_nonneg_iff_analyticAt]
  have hA : 0 ≤ meromorphicOrderAt (fun z => Φ F z - t) (τ : ℂ) := by rw [ord_Φ hF]; exact h
  have hB : 0 ≤ meromorphicOrderAt (fun _ : ℂ => t) (τ : ℂ) := by
    rw [meromorphicOrderAt_const]
    split_ifs <;> simp
  have hm : MeromorphicAt (fun z => Φ F z - t) (τ : ℂ) :=
    (Φ_merAt F τ).sub (MeromorphicAt.const t _)
  have hsum := meromorphicOrderAt_add hm (MeromorphicAt.const t (τ : ℂ))
  have heq : ((fun z => Φ F z - t) + fun _ : ℂ => t) = Φ F := by
    funext z; simp
  rw [heq] at hsum
  exact le_trans (le_min hA hB) hsum

theorem ord_eq_map (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (t : ℂ) {τ : ℍ} (han : AnalyticAt ℂ (Φ F) (τ : ℂ)) :
    ord F t τ = (analyticOrderAt (fun z => Φ F z - t) (τ : ℂ)).map (Nat.cast : ℕ → ℤ) := by
  rw [← ord_Φ hF]
  have ha : AnalyticAt ℂ (fun z => Φ F z - t) (τ : ℂ) := han.sub analyticAt_const
  exact ha.meromorphicOrderAt_eq

theorem pos_map_iff (a : ℕ∞) : (0 : WithTop ℤ) < a.map (Nat.cast : ℕ → ℤ) ↔ a ≠ 0 := by
  induction a with
  | top => simp
  | coe n =>
    rw [ENat.map_coe]
    constructor
    · intro h h0
      have : n = 0 := by exact_mod_cast h0
      subst this
      simp at h
    · intro h
      have hn : n ≠ 0 := by exact_mod_cast h
      have : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      exact_mod_cast this

theorem ord_pos_iff (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (t : ℂ) {τ : ℍ} (han : AnalyticAt ℂ (Φ F) (τ : ℂ)) :
    0 < ord F t τ ↔ Φ F τ = t := by
  have ha : AnalyticAt ℂ (fun z => Φ F z - t) (τ : ℂ) := han.sub analyticAt_const
  rw [ord_eq_map hF t han, pos_map_iff, Ne, ← not_iff_not, not_not, ha.analyticOrderAt_eq_zero]
  simp [sub_eq_zero]

theorem ord_eq_one (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    {t : ℂ} {τ : ℍ} (han : AnalyticAt ℂ (Φ F) (τ : ℂ)) (hval : Φ F τ = t)
    (hd : deriv (Φ F) τ ≠ 0) : ord F t τ = 1 := by
  rw [ord_eq_map hF t han]
  have h1 := han.analyticOrderAt_deriv_add_one
  have h0 : analyticOrderAt (deriv (Φ F)) (τ : ℂ) = 0 := han.deriv.analyticOrderAt_eq_zero.mpr hd
  rw [h0, zero_add, hval] at h1
  rw [← h1]
  simp

theorem ord_eq_coe_of_pos_of_ne_top {t : ℂ} {τ : ℍ} (hpos : 0 < ord F t τ) (hne : ord F t τ ≠ ⊤) :
    ∃ k : ℕ, 0 < k ∧ ord F t τ = (k : ℤ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hn] at hpos
  have hn0 : 0 < n := by exact_mod_cast hpos
  refine ⟨n.toNat, by omega, ?_⟩
  rw [← hn]
  congr 1
  omega

end Orders
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

section Local

variable {F : ℍ → ℂ}

theorem eventually_closedBall_subset {τ₀ : ℍ} {s : Set ℍ} (hs : s ∈ 𝓝 τ₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), Metric.closedBall τ₀ ρ ⊆ s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  exact (Metric.closedBall_subset_ball hρ.2).trans hball

theorem analyticAt_mem_nhds {τ₀ : ℍ} (han : AnalyticAt ℂ (Φ F) ↑τ₀) :
    {z : ℍ | AnalyticAt ℂ (Φ F) ↑z} ∈ 𝓝 τ₀ :=
  continuous_coe.continuousAt.eventually han.eventually_analyticAt

theorem eventually_ne_and_deriv_ne
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hnc : ∀ (t : ℂ) (τ : ℍ), meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    {τ₀ : ℍ} (han : AnalyticAt ℂ (Φ F) ↑τ₀) (t₀ : ℂ) :
    ∀ᶠ w in 𝓝[≠] (τ₀ : ℂ), Φ F w ≠ t₀ ∧ deriv (Φ F) w ≠ 0 := by
  have h1 : ∀ᶠ w in 𝓝[≠] (τ₀ : ℂ), Φ F w ≠ t₀ := by
    have ha : AnalyticAt ℂ (fun z => Φ F z - t₀) ↑τ₀ := han.sub analyticAt_const
    rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hnc t₀ τ₀
      show ord F t₀ τ₀ = ⊤
      rw [← ord_Φ hF, meromorphicOrderAt_eq_top_iff]
      exact eventually_nhdsWithin_of_eventually_nhds h
    · exact h.mono fun w hw => sub_ne_zero.mp hw
  have h2 : ∀ᶠ w in 𝓝[≠] (τ₀ : ℂ), deriv (Φ F) w ≠ 0 := by
    rcases han.deriv.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h.and han.eventually_analyticAt)
      have hconst : ∀ y ∈ Metric.ball (τ₀ : ℂ) ε, Φ F y = Φ F τ₀ := fun y hy =>
        Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
          (fun w hw => (hball w hw).2.differentiableAt.differentiableWithinAt)
          (fun w hw => (hball w hw).1) hy (Metric.mem_ball_self hε)
      apply hnc (Φ F τ₀) τ₀
      show ord F (Φ F τ₀) τ₀ = ⊤
      rw [← ord_Φ hF, meromorphicOrderAt_eq_top_iff]
      have : ∀ᶠ w in 𝓝 (τ₀ : ℂ), Φ F w - Φ F τ₀ = 0 := by
        filter_upwards [Metric.ball_mem_nhds _ hε] with w hw
        rw [hconst w hw, sub_self]
      exact eventually_nhdsWithin_of_eventually_nhds this
    · exact h
  exact h1.and h2

theorem punctured_mem_nhds
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hnc : ∀ (t : ℂ) (τ : ℍ), meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    {τ₀ : ℍ} (han : AnalyticAt ℂ (Φ F) ↑τ₀) (t₀ : ℂ) :
    {z : ℍ | z ≠ τ₀ → Φ F ↑z ≠ t₀ ∧ deriv (Φ F) ↑z ≠ 0} ∈ 𝓝 τ₀ := by
  have := (tendsto_coe_nhdsNE τ₀).eventually (eventually_ne_and_deriv_ne hF hnc han t₀)
  exact eventually_nhdsWithin_iff.mp this

theorem stab_mem_nhds (τ₀ : ℍ) :
    ∃ V ∈ 𝓝 τ₀, ∀ g : SL(2, ℤ), ∀ z ∈ V, g • z ∈ V → g • τ₀ = τ₀ := by
  obtain ⟨V, hV, h⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self (↥𝒮ℒ) τ₀
  exact ⟨V, hV, fun g z hz hgz => h (toSLsub g) ⟨g • z, ⟨z, hz, rfl⟩, hgz⟩⟩

theorem eventually_separated {Γ : Subgroup SL(2, ℤ)} {τ₁ τ₂ : ℍ}
    (h : ∀ γ ∈ Γ, γ • τ₁ ≠ τ₂) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ γ ∈ Γ, ∀ z ∈ Metric.ball τ₁ ρ, γ • z ∉ Metric.ball τ₂ ρ := by
  classical
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := ↥𝒮ℒ)
    (isCompact_closedBall τ₁ 1) (isCompact_closedBall τ₂ 1)
  set T : Set ↥𝒮ℒ :=
    {g | ((g • ·) '' Metric.closedBall τ₁ 1 ∩ Metric.closedBall τ₂ 1).Nonempty} with hT
  have hδ : ∃ δ > 0, ∀ g ∈ T, g • τ₁ ≠ τ₂ → δ ≤ dist (g • τ₁) τ₂ := by
    let D : Finset ℝ :=
      (hfin.toFinset.filter fun g => g • τ₁ ≠ τ₂).image fun g => dist (g • τ₁) τ₂
    by_cases hD : D.Nonempty
    · refine ⟨D.min' hD, ?_, fun g hg hne => D.min'_le _ (Finset.mem_image.mpr
        ⟨g, Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hg, hne⟩, rfl⟩)⟩
      obtain ⟨g, hg, hgeq⟩ := Finset.mem_image.mp (D.min'_mem hD)
      rw [← hgeq]
      exact dist_pos.mpr (Finset.mem_filter.mp hg).2
    · exact ⟨1, one_pos, fun g hg hne => (hD ⟨_, Finset.mem_image.mpr
        ⟨g, Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hg, hne⟩, rfl⟩⟩).elim⟩
  obtain ⟨δ, hδ, hδle⟩ := hδ
  have hm : (0 : ℝ) < min 1 (δ / 2) := lt_min one_pos (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hm] with ρ hρ γ hγ z hz hγz
  have hρ1 : ρ < 1 := hρ.2.trans_le (min_le_left _ _)
  have hρδ : ρ < δ / 2 := hρ.2.trans_le (min_le_right _ _)
  rw [Metric.mem_ball] at hz hγz
  have hmemT : toSLsub γ ∈ T := by
    refine ⟨γ • z, ⟨z, ?_, rfl⟩, ?_⟩
    · exact Metric.mem_closedBall.mpr (by linarith)
    · exact Metric.mem_closedBall.mpr (show dist (γ • z) τ₂ ≤ 1 by linarith)
  have hne : toSLsub γ • τ₁ ≠ τ₂ := h γ hγ
  have h1 := hδle _ hmemT hne
  rw [toSLsub_smul] at h1
  have h2 : dist (γ • τ₁) τ₂ ≤ dist (γ • τ₁) (γ • z) + dist (γ • z) τ₂ := dist_triangle _ _ _
  rw [dist_smul_smul, dist_comm τ₁ z] at h2
  linarith

end Local
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

section Stabilizers

theorem neg_one_smul (τ : ℍ) : (-1 : SL(2, ℤ)) • τ = τ := negOne_smul τ

theorem neg_smul' (g : SL(2, ℤ)) (z : ℍ) : (-g) • z = g • z := neg_smul_eq g z

theorem neg_one_mem_sup : (-1 : SL(2, ℤ)) ∈ Γ′ := negOne_mem_sup

theorem inv_sup {β : Sort*} {u : ℍ → β} (hu : ∀ γ ∈ Γ, ∀ τ : ℍ, u (γ • τ) = u τ) :
    ∀ g ∈ Γ′, ∀ τ : ℍ, u (g • τ) = u τ := forall_mem_sup hu

theorem two_le_card_stabilizer (τ : ℍ) :
    2 ≤ Nat.card (MulAction.stabilizer Γ′ τ) := two_le_card_stabilizer_sup (Γ := Γ) τ

end Stabilizers
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

section SimpleZeros

variable [Γ.FiniteIndex] {F : ℍ → ℂ}

theorem card_stabilizer_eq_two
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) {t : ℂ} {τ : ℍ}
    (h1 : ord F t τ = 1) :
    Nat.card (MulAction.stabilizer Γ′ τ) = 2 :=
  card_stabilizer_sup_eq_two hΓ h1

theorem card_stabilizer_eq_k
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) {t : ℂ} {τ : ℍ} (h1 : ord F t τ = 1) :
    Nat.card (MulAction.stabilizer Γ τ) = Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ))) :=
  natCard_stabilizer_eq_k hΓ h1

theorem period_eq_zero_of_smul_eq (γ : Γ) {c : ℍ}
    (hc : (γ : SL(2, ℤ)) • c = c) : ModularCurve.periodOf Γ γ = 0 := by
  have := ModularCurve.periodAlongOf_smul_sub_periodAlongOf_eq_periodOf Γ γ c
  rw [hc, sub_self] at this
  exact this.symm

theorem periodAlong_smul_of_smul_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Γ)
    {c : ℍ} (hc : γ • c = c) (z : ℍ) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I (γ • z) =
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I z := by
  have h := ModularCurve.periodAlongOf_smul_sub_periodAlongOf_eq_periodOf Γ ⟨γ, hγ⟩ z
  rw [period_eq_zero_of_smul_eq (Γ := Γ) ⟨γ, hγ⟩ hc] at h
  exact sub_eq_zero.mp h

theorem periodAlong_smul_sub_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Γ)
    (z : ℍ) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I (γ • z) -
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I z ∈ ModularCurve.periodLatticeOf Γ := by
  rw [show γ • z = ((⟨γ, hγ⟩ : Γ) : SL(2, ℤ)) • z from rfl,
    ModularCurve.periodAlongOf_smul_sub_periodAlongOf_eq_periodOf Γ ⟨γ, hγ⟩ z]
  exact ModularCurve.periodOf_mem_periodLatticeOf Γ _

theorem periodAlong_out_sub_mem (z : ℍ) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I
        (Quotient.mk (MulAction.orbitRel (Γ) ℍ) z).out -
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I z ∈ ModularCurve.periodLatticeOf Γ := by
  obtain ⟨γ, hγ⟩ := Quotient.mk_out (s := MulAction.orbitRel (Γ) ℍ) z
  rw [← hγ]
  exact periodAlong_smul_sub_mem γ.2 z

theorem periodAlong_eq_sub (f : CuspForm Γ 2)
    {E : ℍ → ℂ} (hE : ∀ τ : ℍ, HasDerivAt (E ∘ ofComplex) (f τ) ↑τ) (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = E τ₁ - E τ₀ :=
  ModularCurve.periodAlongOf_apply_eq_sub_of_hasDerivAt Γ f hE τ₀ τ₁

theorem eventually_ord_eq_zero
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) {t : ℂ}
    (hne : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤) (τ : ℍ) :
    ∀ᶠ w in 𝓝[≠] τ, ord F t w = 0 := by
  have hft : MeromorphicAt (fsub F t) (τ : ℂ) := merAt_fsub hF t τ
  have h1 := hft.eventually_analyticAt
  have h2 := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hft).1 (hne τ)
  have h3 : ∀ᶠ y in 𝓝[≠] (τ : ℂ), meromorphicOrderAt (fsub F t) y = 0 := by
    filter_upwards [h1, h2] with y hy1 hy2
    exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hy1.meromorphicAt).1
      ⟨_, hy2, hy1.continuousAt.continuousWithinAt.tendsto⟩
  exact (tendsto_coe_nhdsNE τ).eventually h3

theorem finite_inter_of_isCompact
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) {t : ℂ}
    (hne : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    {K : Set ℍ} (hK : IsCompact K) : ({τ : ℍ | ord F t τ ≠ 0} ∩ K).Finite := by
  obtain ⟨s, -, hcover⟩ := hK.elim_nhds_subcover (fun x => {w | w ≠ x → ord F t w = 0})
    (fun x _ => by
      have := eventually_ord_eq_zero hF hne x
      rw [eventually_nhdsWithin_iff] at this
      exact this)
  refine (s.finite_toSet).subset ?_
  rintro τ ⟨hτS, hτK⟩
  obtain ⟨x, hx, hτx⟩ := Set.mem_iUnion₂.mp (hcover hτK)
  by_contra hmem
  have hτx' : τ ≠ x := fun h => hmem (h ▸ hx)
  exact hτS (hτx hτx')

end SimpleZeros
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

section Regroup

theorem logDeriv_expansion {Φ G : ℂ → ℂ} {p t : ℂ} {k : ℕ}
    (hΦ : AnalyticAt ℂ Φ p) (hG : AnalyticAt ℂ G p)
    (hk : analyticOrderAt (fun z => Φ z - t) p = k) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ z in 𝓝[≠] p, G z * deriv Φ z / (Φ z - t) = (k * G p) / (z - p) + g z := by
  have hΦt : AnalyticAt ℂ (fun z => Φ z - t) p := hΦ.sub analyticAt_const
  obtain ⟨q, hq, hq0, hqe⟩ := (hΦt.analyticOrderAt_eq_natCast).mp hk

  have hG1 : (1 : ℕ) ≤ analyticOrderAt (fun z => G z - G p) p := by
    have hG' : AnalyticAt ℂ (fun z => G z - G p) p := hG.sub analyticAt_const
    rw [Nat.cast_one, ENat.one_le_iff_ne_zero, Ne, hG'.analyticOrderAt_eq_zero]
    exact fun h => h (sub_self _)
  obtain ⟨r, hr, hre⟩ := (natCast_le_analyticOrderAt (hG.sub analyticAt_const)).mp hG1
  refine ⟨fun z => k * r z + G z * deriv q z / q z, ?_, ?_⟩
  · exact (analyticAt_const.mul hr).add ((hG.mul hq.deriv).div hq hq0)

  have hqa : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ q z := hq.eventually_analyticAt
  have hqne : ∀ᶠ z in 𝓝 p, q z ≠ 0 := hq.continuousAt.eventually_ne hq0
  have hqe' : ∀ᶠ z in 𝓝 p, ∀ᶠ w in 𝓝 z, Φ w - t = (w - p) ^ k • q w := hqe.eventually_nhds
  have hall := (hqa.and (hqne.and (hqe'.and (hqe.and hre))))
  refine (eventually_nhdsWithin_of_eventually_nhds hall).mp ?_
  refine eventually_nhdsWithin_of_forall fun z (hz : z ≠ p) ⟨hqa, hqne, hqe', hqe, hre⟩ => ?_
  have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz

  have hΦeq : Φ =ᶠ[𝓝 z] fun w => (w - p) ^ k * q w + t := by
    filter_upwards [hqe'] with w hw
    rw [smul_eq_mul] at hw
    linear_combination hw
  have hd : deriv Φ z = k * (z - p) ^ (k - 1) * q z + (z - p) ^ k * deriv q z := by
    rw [hΦeq.deriv_eq]
    have h1 : HasDerivAt (fun w : ℂ => (w - p) ^ k) (k * (z - p) ^ (k - 1)) z := by
      have h__af := ((hasDerivAt_id z |>.sub_const p).pow k)
      simp at h__af
      exact h__af
    have h2 : HasDerivAt q (deriv q z) z := hqa.differentiableAt.hasDerivAt
    have h3 : HasDerivAt (fun w : ℂ => (w - p) ^ k * q w + t)
        (k * (z - p) ^ (k - 1) * q z + (z - p) ^ k * deriv q z) z := (h1.mul h2).add_const t
    exact h3.deriv
  rw [smul_eq_mul] at hqe hre
  rw [hd, hqe]
  have hGz : G z = G p + (z - p) * r z := by
    have : G z - G p = (z - p) ^ 1 * r z := hre
    linear_combination this

  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · have hpow : (z - p) ^ k = (z - p) * (z - p) ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]
    field_simp
    rw [hGz]
    ring

theorem subgroup_smul_def {G : Subgroup SL(2, ℤ)} {H : Subgroup G} (h : H) (z : ℍ) :
    h • z = ((h : G) : SL(2, ℤ)) • z := rfl

theorem card_stabilizer_subgroup_eq_two {G : Subgroup SL(2, ℤ)} (hneg : (-1 : SL(2, ℤ)) ∈ G)
    (H : Subgroup G) [Finite H] (hH : (⟨-1, hneg⟩ : G) ∈ H) (r : ℍ)
    (hcard : Nat.card (stabilizer G r) = 2) : Nat.card (stabilizer H r) = 2 := by
  haveI : Finite (stabilizer G r) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  apply le_antisymm
  · refine le_of_le_of_eq (Nat.card_le_card_of_injective
      (fun s : stabilizer H r => (⟨((s : H) : G), s.2⟩ : stabilizer G r)) ?_) hcard
    intro a b hab
    have := congrArg Subtype.val hab
    ext : 2
    exact this
  · have hnt : Nontrivial (stabilizer H r) := by
      refine ⟨⟨1, ⟨⟨⟨-1, hneg⟩, hH⟩, ?_⟩, ?_⟩⟩
      · show ((-1 : SL(2, ℤ))) • r = r
        ext1; simp
      · intro h
        have := congrArg (fun s : stabilizer H r => (((s : H) : G) : SL(2, ℤ)) 0 0) h
        simp at this
    have := Finite.one_lt_card_iff_nontrivial.mpr hnt
    omega

open scoped Classical in

theorem sum_eq_card_mul_sum_image {G : Subgroup SL(2, ℤ)} (hneg : (-1 : SL(2, ℤ)) ∈ G) (c : ℍ)
    [Finite (stabilizer G c)]
    (Z : Finset ℍ) (hZ : ∀ h ∈ stabilizer G c, ∀ z ∈ Z, (h : SL(2, ℤ)) • z ∈ Z)
    (hcard : ∀ z ∈ Z, Nat.card (stabilizer G z) = 2)
    (u : ℍ → ℂ) (hu : ∀ h ∈ stabilizer G c, ∀ z ∈ Z, u ((h : SL(2, ℤ)) • z) = u z) :
    ∑ z ∈ Z, u z =
      (Nat.card (stabilizer G c) / 2 : ℕ) *
        ∑ r ∈ Z.image (fun z => (Quotient.mk (orbitRel (stabilizer G c) ℍ) z).out), u r := by
  set H := stabilizer G c
  set rep : ℍ → ℍ := fun z => (Quotient.mk (orbitRel H ℍ) z).out with hrep_def
  have hrep_orb : ∀ z : ℍ, ∃ h : H, h • z = rep z := fun z => Quotient.mk_out (s := orbitRel H ℍ) z
  have hrep_mk : ∀ z : ℍ, Quotient.mk (orbitRel H ℍ) (rep z) = Quotient.mk (orbitRel H ℍ) z :=
    fun z => Quotient.out_eq _
  have hrepZ : ∀ z ∈ Z, rep z ∈ Z := by
    intro z hz
    obtain ⟨h, hh⟩ := hrep_orb z
    rw [← hh, subgroup_smul_def]
    exact hZ _ h.2 z hz
  have hurep : ∀ z ∈ Z, u (rep z) = u z := by
    intro z hz
    obtain ⟨h, hh⟩ := hrep_orb z
    rw [← hh, subgroup_smul_def]
    exact hu _ h.2 z hz
  have hreprep : ∀ z, rep (rep z) = rep z := fun z => by
    simp only [hrep_def, Quotient.out_eq]

  have hfib : ∀ z₀ ∈ Z, (↑(Z.filter fun z => rep z = rep z₀) : Set ℍ) = orbit H (rep z₀) := by
    intro z₀ hz₀
    ext z
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, hz⟩
      rw [← orbitRel_apply, ← Quotient.eq (r := orbitRel H ℍ), ← hrep_mk z, hz, hrep_mk]
    · intro hz
      have hz' := hz
      rw [← orbitRel_apply, ← Quotient.eq (r := orbitRel H ℍ), hrep_mk] at hz'
      obtain ⟨h, rfl⟩ := hz
      refine ⟨?_, ?_⟩
      · show h • rep z₀ ∈ Z
        rw [subgroup_smul_def]; exact hZ _ h.2 _ (hrepZ z₀ hz₀)
      · show (Quotient.mk (orbitRel H ℍ) (h • rep z₀)).out = rep z₀
        rw [hz']
  have hH1 : (⟨-1, hneg⟩ : G) ∈ H := by
    show ((-1 : SL(2, ℤ))) • c = c
    ext1; simp
  have hcardfib : ∀ z₀ ∈ Z, (Z.filter fun z => rep z = rep z₀).card = Nat.card H / 2 := by
    intro z₀ hz₀
    have h2 := card_stabilizer_subgroup_eq_two hneg H hH1 (rep z₀) (hcard _ (hrepZ z₀ hz₀))
    have hidx := (stabilizer H (rep z₀)).index_mul_card
    rw [h2, MulAction.index_stabilizer, ← hfib z₀ hz₀, Set.ncard_coe_finset] at hidx
    symm
    exact Nat.div_eq_of_eq_mul_left (by norm_num) hidx.symm

  rw [← Finset.sum_fiberwise_of_maps_to (g := rep) (t := Z.image rep)
    (fun z hz => Finset.mem_image_of_mem rep hz), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hr
  have : ∀ z ∈ Z.filter (fun z => rep z = rep z₀), u z = u (rep z₀) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [← hz.2, hurep z hz.1]
  rw [Finset.sum_congr rfl this, Finset.sum_const, hcardfib z₀ hz₀, nsmul_eq_mul]

end Regroup
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

section Discs

def eC (c : ℍ) (ρ : ℝ) : ℂ := ((c.center ρ : ℍ) : ℂ)

def eR (c : ℍ) (ρ : ℝ) : ℝ := c.im * Real.sinh ρ

theorem eR_pos (c : ℍ) {ρ : ℝ} (hρ : 0 < ρ) : 0 < eR c ρ :=
  mul_pos c.im_pos (Real.sinh_pos_iff.mpr hρ)

private theorem _root_.ModularCurve.FibreConstOf.image_coe_closedBall (c : ℍ) (ρ : ℝ) :
    ((↑) : ℍ → ℂ) '' Metric.closedBall c ρ = Metric.closedBall (eC c ρ) (eR c ρ) :=
  UpperHalfPlane.image_coe_closedBall c ρ

p2m_export "ModularCurve.FibreConstOf" "image_coe_closedBall"
private theorem _root_.ModularCurve.FibreConstOf.image_coe_ball (c : ℍ) (ρ : ℝ) :
    ((↑) : ℍ → ℂ) '' Metric.ball c ρ = Metric.ball (eC c ρ) (eR c ρ) :=
  UpperHalfPlane.image_coe_ball c ρ

p2m_export "ModularCurve.FibreConstOf" "image_coe_ball"
private theorem _root_.ModularCurve.FibreConstOf.image_coe_sphere (c : ℍ) (ρ : ℝ) :
    ((↑) : ℍ → ℂ) '' Metric.sphere c ρ = Metric.sphere (eC c ρ) (eR c ρ) :=
  UpperHalfPlane.image_coe_sphere c ρ

p2m_export "ModularCurve.FibreConstOf" "image_coe_sphere"
theorem forall_closedBall {c : ℍ} {ρ : ℝ} {P : ℂ → Prop}
    (h : ∀ z ∈ Metric.closedBall c ρ, P ↑z) : ∀ w ∈ Metric.closedBall (eC c ρ) (eR c ρ), P w := by
  intro w hw
  rw [← image_coe_closedBall] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact h z hz

theorem forall_sphere {c : ℍ} {ρ : ℝ} {P : ℂ → Prop}
    (h : ∀ z ∈ Metric.sphere c ρ, P ↑z) : ∀ w ∈ Metric.sphere (eC c ρ) (eR c ρ), P w := by
  intro w hw
  rw [← image_coe_sphere] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact h z hz

theorem coe_mem_ball {c : ℍ} {ρ : ℝ} {z : ℍ} (hz : z ∈ Metric.ball c ρ) :
    (z : ℂ) ∈ Metric.ball (eC c ρ) (eR c ρ) := by
  rw [← image_coe_ball]; exact Set.mem_image_of_mem _ hz

theorem cuspForm_analyticAt {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => f (ofComplex z)) (τ : ℂ) := by
  have h : DifferentiableOn ℂ ((⇑f) ∘ ofComplex) U :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact h.analyticAt (isOpen_U.mem_nhds τ.im_pos)

theorem coe_ofComplex {z : ℂ} (hz : z ∈ U) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

theorem primitive_hasDerivAt {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) {E : ℍ → ℂ}
    (hE : ∀ τ : ℍ, HasDerivAt (E ∘ ofComplex) (f τ) ↑τ) (a : ℂ) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w : ℂ => E (ofComplex w) - a) (f (ofComplex z)) z := by
  have := hE (ofComplex z)
  rw [coe_ofComplex hz] at this
  exact this.sub_const a

theorem primitive_analyticAt {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) {E : ℍ → ℂ}
    (hE : ∀ τ : ℍ, HasDerivAt (E ∘ ofComplex) (f τ) ↑τ) (a : ℂ) (τ : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => E (ofComplex w) - a) (τ : ℂ) := by
  have h : DifferentiableOn ℂ (fun w : ℂ => E (ofComplex w) - a) U := fun z hz =>
    (primitive_hasDerivAt f hE a hz).differentiableAt.differentiableWithinAt
  exact h.analyticAt (isOpen_U.mem_nhds τ.im_pos)

theorem primitive_deriv {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) {E : ℍ → ℂ}
    (hE : ∀ τ : ℍ, HasDerivAt (E ∘ ofComplex) (f τ) ↑τ) (a : ℂ) (τ : ℍ) :
    deriv (fun w : ℂ => E (ofComplex w) - a) (τ : ℂ) = f τ := by
  have := (primitive_hasDerivAt f hE a (z := (τ : ℂ)) τ.im_pos).deriv
  rwa [ofComplex_apply] at this

end Discs
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

section CircleEval

theorem circleIntegral_mul_logDeriv_eq {Φ G : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R) (t : ℂ)
    (Z : Finset ℂ) (hZ : ∀ a ∈ Z, a ∈ Metric.ball z₀ R)
    (hΦ : ∀ z ∈ Metric.closedBall z₀ R, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ Metric.closedBall z₀ R, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.closedBall z₀ R, z ∉ Z → Φ z ≠ t)
    (k : ℂ → ℕ) (hk : ∀ a ∈ Z, analyticOrderAt (fun z => Φ z - t) a = k a) :
    (∮ z in C(z₀, R), G z * deriv Φ z / (Φ z - t)) =
      2 * Real.pi * Complex.I * ∑ a ∈ Z, ((k a : ℂ) * G a) := by
  refine Complex.circleIntegral_eq_sum_residue_of_simplePole hR
    (fun z => G z * deriv Φ z / (Φ z - t)) (fun a => k a * G a) Z hZ ?_ ?_
  · intro z hz hzZ
    exact ((hG z hz).mul (hΦ z hz).deriv).div ((hΦ z hz).sub analyticAt_const)
      (sub_ne_zero.mpr (hne z hz hzZ))
  · intro a ha
    have haR : a ∈ Metric.closedBall z₀ R := Metric.ball_subset_closedBall (hZ a ha)
    exact logDeriv_expansion (hΦ a haR) (hG a haR) (hk a ha)

theorem sum_circleIntegral_eq_of_deriv_eq_zero {α : Type*} (ι : Finset α) (e : α → ℂ)
    (zc : α → ℂ) (R : α → ℝ) (hR : ∀ i ∈ ι, 0 < R i) {Φ G : ℂ → ℂ} {t₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hΦ : ∀ i ∈ ι, ∀ z ∈ Metric.sphere (zc i) (R i), AnalyticAt ℂ Φ z)
    (hG : ∀ i ∈ ι, ∀ z ∈ Metric.sphere (zc i) (R i), AnalyticAt ℂ G z)
    (hne : ∀ t ∈ Metric.ball t₀ ε, ∀ i ∈ ι, ∀ z ∈ Metric.sphere (zc i) (R i), Φ z ≠ t)
    (hvan : ∀ t ∈ Metric.ball t₀ ε, t ≠ t₀ →
      ∑ i ∈ ι, e i * ∮ z in C(zc i, R i), deriv G z / (Φ z - t) = 0)
    {t : ℂ} (ht : t ∈ Metric.ball t₀ ε) :
    ∑ i ∈ ι, e i * ∮ z in C(zc i, R i), G z * deriv Φ z / (Φ z - t) =
      ∑ i ∈ ι, e i * ∮ z in C(zc i, R i), G z * deriv Φ z / (Φ z - t₀) := by
  set T : ℂ → ℂ := fun s => ∑ i ∈ ι, e i * ∮ z in C(zc i, R i), G z * deriv Φ z / (Φ z - s)
    with hT
  set T' : ℂ → ℂ := fun s => ∑ i ∈ ι, e i * ∮ z in C(zc i, R i), deriv G z / (Φ z - s) with hT'
  have hder : ∀ s ∈ Metric.ball t₀ ε, HasDerivAt T (T' s) s := by
    intro s hs
    exact HasDerivAt.fun_sum (u := ι)
      (A := fun i s => e i * ∮ z in C(zc i, R i), G z * deriv Φ z / (Φ z - s))
      (A' := fun i => e i * ∮ z in C(zc i, R i), deriv G z / (Φ z - s))
      fun i hi => (Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub (hR i hi) (hΦ i hi)
        (hG i hi) (hne s hs i hi)).const_mul (e i)
  have hdiff : DifferentiableOn ℂ T (Metric.ball t₀ ε) := fun s hs =>
    (hder s hs).differentiableAt.differentiableWithinAt
  have hderiv_off : ∀ s ∈ Metric.ball t₀ ε, s ≠ t₀ → deriv T s = 0 := by
    intro s hs hs0
    rw [(hder s hs).deriv]
    exact hvan s hs hs0
  have hderiv_at : deriv T t₀ = 0 := by
    have hTa : AnalyticAt ℂ T t₀ :=
      hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    have hcont : ContinuousAt (deriv T) t₀ := hTa.deriv.continuousAt
    have hev : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝[≠] t₀] deriv T := by
      have h1 : ∀ᶠ s in 𝓝[≠] t₀, s ∈ Metric.ball t₀ ε :=
        eventually_nhdsWithin_of_eventually_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
      filter_upwards [h1, self_mem_nhdsWithin] with s hs hs0
      exact (hderiv_off s hs hs0).symm
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev)
  have hEq : (Metric.ball t₀ ε).EqOn (deriv T) 0 := by
    intro s hs
    by_cases hs0 : s = t₀
    · rw [hs0]; exact hderiv_at
    · exact hderiv_off s hs hs0
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball t₀ ε).isPreconnected hdiff hEq
    ht (Metric.mem_ball_self hε)

end CircleEval
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

section Prelim

variable {F : ℍ → ℂ} {t₀ : ℂ}

theorem eventually_sphere_ne {c : ℍ} {ρ : ℝ}
    (hA : ∀ z ∈ Metric.closedBall c ρ, AnalyticAt ℂ (Φ F) ↑z)
    (hne : ∀ z ∈ Metric.sphere c ρ, Φ F ↑z ≠ t₀) :
    ∀ᶠ t in 𝓝 t₀, ∀ z ∈ Metric.sphere c ρ, Φ F ↑z ≠ t := by
  apply (isCompact_sphere c ρ).eventually_forall_of_forall_eventually
  intro z hz
  have h1 : ContinuousAt (fun p : ℂ × ℍ => Φ F ↑p.2) (t₀, z) :=
    (hA z (Metric.sphere_subset_closedBall hz)).continuousAt.comp_of_eq
      (continuous_coe.comp continuous_snd).continuousAt rfl
  have hc : ContinuousAt (fun p : ℂ × ℍ => Φ F ↑p.2 - p.1) (t₀, z) := h1.sub continuousAt_fst
  have h0 : (fun p : ℂ × ℍ => Φ F ↑p.2 - p.1) (t₀, z) ≠ 0 := sub_ne_zero.mpr (hne z hz)
  exact (hc.eventually_ne h0).mono fun p hp h => hp (by simp only [h, sub_self])

end Prelim
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

section Main

variable [Γ.FiniteIndex] {F : ℍ → ℂ}

local notation "X" => Quotient (MulAction.orbitRel Γ ℍ)
local notation "πq" => Quotient.mk (MulAction.orbitRel Γ ℍ)

open scoped Classical in

def Zf (F : ℍ → ℂ) (t : ℂ) (c : ℍ) (ρ : ℝ) : Finset ℍ :=
  if h : {z : ℍ | z ∈ Metric.closedBall c ρ ∧ Φ F ↑z = t}.Finite then h.toFinset else ∅

def rep (Γ : Subgroup SL(2, ℤ)) (c z : ℍ) : ℍ :=
  (Quotient.mk (orbitRel (stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) c) ℍ) z).out

open scoped Classical in

def Sf (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (t : ℂ) (c : ℍ) (ρ : ℝ) : Finset ℍ := (Zf F t c ρ).image (rep Γ c)

theorem rep_spec (c z : ℍ) : ∃ h ∈ stabilizer Γ′ c, (h : SL(2, ℤ)) • z = rep Γ c z := by
  obtain ⟨h, hh⟩ := Quotient.mk_out (s := orbitRel (stabilizer Γ′ c) ℍ) z
  exact ⟨h, h.2, hh⟩

theorem rep_smul (c z : ℍ) {h : ↥Γ′} (hh : h ∈ stabilizer Γ′ c) :
    rep Γ c ((h : SL(2, ℤ)) • z) = rep Γ c z := by
  unfold rep
  congr 1
  apply Quotient.sound
  show (orbitRel (stabilizer Γ′ c) ℍ) ((h : SL(2, ℤ)) • z) z
  rw [orbitRel_apply]
  exact ⟨⟨h, hh⟩, rfl⟩

theorem rep_rep (c z : ℍ) : rep Γ c (rep Γ c z) = rep Γ c z := by
  simp only [rep, Quotient.out_eq]

open scoped Classical in
theorem mem_Sf {t : ℂ} {c : ℍ} {ρ : ℝ} {r : ℍ} :
    r ∈ Sf Γ F t c ρ ↔ ∃ z ∈ Zf F t c ρ, rep Γ c z = r := Finset.mem_image

theorem rep_eq_self_of_mem_Sf {t : ℂ} {c : ℍ} {ρ : ℝ} {r : ℍ} (hr : r ∈ Sf Γ F t c ρ) :
    rep Γ c r = r := by
  obtain ⟨z, -, rfl⟩ := mem_Sf.mp hr
  exact rep_rep c z

theorem analyticOrderAt_eq_of_map_eq {a : ℕ∞} {k : ℕ}
    (h : a.map (Nat.cast : ℕ → ℤ) = ((k : ℤ) : WithTop ℤ)) : a = k := by
  induction a with
  | top => simp at h
  | coe n =>
    rw [ENat.map_coe] at h
    have : (n : ℤ) = k := by exact_mod_cast h
    exact_mod_cast this

structure GoodRadius (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (t₀ : ℂ)
    (ι : Finset (Quotient (MulAction.orbitRel (Γ) ℍ))) (ρ : ℝ) :
    Prop where
  pos : 0 < ρ
  fib : ∀ ξ ∈ ι, 0 < ord F t₀ ξ.out
  all : ∀ τ : ℍ, 0 < ord F t₀ τ →
    Quotient.mk (MulAction.orbitRel (Γ) ℍ) τ ∈ ι
  R1 : ∀ ξ ∈ ι, ∀ z ∈ Metric.closedBall ξ.out ρ, AnalyticAt ℂ (Φ F) ↑z
  R2 : ∀ ξ ∈ ι, ∀ z ∈ Metric.closedBall ξ.out ρ, z ≠ ξ.out →
    Φ F ↑z ≠ t₀ ∧ deriv (Φ F) ↑z ≠ 0
  R3 : ∀ ξ ∈ ι, ∀ γ ∈ Γ, ∀ z ∈ Metric.ball ξ.out ρ,
    γ • z ∈ Metric.ball ξ.out ρ → γ • ξ.out = ξ.out
  R4 : ∀ ξ ∈ ι, ∀ ξ' ∈ ι, ξ ≠ ξ' → ∀ γ ∈ Γ,
    ∀ z ∈ Metric.ball ξ.out ρ, γ • z ∉ Metric.ball ξ'.out ρ

structure GoodParam (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (t₀ : ℂ)
    (ι : Finset (Quotient (MulAction.orbitRel (Γ) ℍ))) (ρ : ℝ)
    (t : ℂ) : Prop where
  ne : t ≠ t₀
  near : ∀ τ : ℍ, 0 < ord F t τ →
    ∃ γ ∈ Γ, ∃ ξ ∈ ι, γ • τ ∈ Metric.ball ξ.out ρ
  sph : ∀ ξ ∈ ι, ∀ z ∈ Metric.sphere ξ.out ρ, Φ F ↑z ≠ t
  cusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
    Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)

variable
  (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
  (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
  (hnc : ∀ (t : ℂ) (τ : ℍ), meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
  {t₀ : ℂ}

include hF hΓ hnc

theorem analyticOrderAt_eq_of_ord_eq {t : ℂ} {τ : ℍ} (han : AnalyticAt ℂ (Φ F) ↑τ) {k : ℕ}
    (h : ord F t τ = (k : ℤ)) : analyticOrderAt (fun z => Φ F z - t) ↑τ = k := by
  rw [ord_eq_map hF t han] at h
  exact analyticOrderAt_eq_of_map_eq h

theorem finite_Zset (t : ℂ) (c : ℍ) (ρ : ℝ)
    (hA : ∀ z ∈ Metric.closedBall c ρ, AnalyticAt ℂ (Φ F) ↑z) :
    {z : ℍ | z ∈ Metric.closedBall c ρ ∧ Φ F ↑z = t}.Finite := by
  refine (finite_inter_of_isCompact hF (hnc t) (isCompact_closedBall c ρ)).subset ?_
  rintro z ⟨hz, hzt⟩
  exact ⟨ne_of_gt ((ord_pos_iff hF t (hA z hz)).mpr hzt), hz⟩

theorem mem_Zf {t : ℂ} {c : ℍ} {ρ : ℝ}
    (hA : ∀ z ∈ Metric.closedBall c ρ, AnalyticAt ℂ (Φ F) ↑z) {z : ℍ} :
    z ∈ Zf F t c ρ ↔ z ∈ Metric.closedBall c ρ ∧ Φ F ↑z = t := by
  rw [Zf, dif_pos (finite_Zset hF hΓ hnc t c ρ hA), Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem mem_Zf_iff_ord_pos {t : ℂ} {c : ℍ} {ρ : ℝ}
    (hA : ∀ z ∈ Metric.closedBall c ρ, AnalyticAt ℂ (Φ F) ↑z) {z : ℍ} :
    z ∈ Zf F t c ρ ↔ z ∈ Metric.closedBall c ρ ∧ 0 < ord F t z := by
  rw [mem_Zf hF hΓ hnc hA]
  constructor
  · rintro ⟨hz, hzt⟩; exact ⟨hz, (ord_pos_iff hF t (hA z hz)).mpr hzt⟩
  · rintro ⟨hz, hzt⟩; exact ⟨hz, (ord_pos_iff hF t (hA z hz)).mp hzt⟩

theorem smul_mem_Zf {t : ℂ} {c : ℍ} {ρ : ℝ}
    (hA : ∀ z ∈ Metric.closedBall c ρ, AnalyticAt ℂ (Φ F) ↑z)
    {h : ↥Γ′} (hh : h ∈ stabilizer Γ′ c) {z : ℍ} (hz : z ∈ Zf F t c ρ) :
    (h : SL(2, ℤ)) • z ∈ Zf F t c ρ := by
  rw [mem_Zf_iff_ord_pos hF hΓ hnc hA] at hz ⊢
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall] at hz ⊢
    have hc : (h : SL(2, ℤ)) • c = c := hh
    calc dist ((h : SL(2, ℤ)) • z) c = dist ((h : SL(2, ℤ)) • z) ((h : SL(2, ℤ)) • c) := by
            rw [hc]
      _ = dist z c := dist_smul_smul _ z c
      _ ≤ ρ := hz.1
  · rw [ord_smul (forall_mem_sup hΓ) (h : SL(2, ℤ)) h.2]
    exact hz.2

theorem rep_mem_Zf {t : ℂ} {c : ℍ} {ρ : ℝ}
    (hA : ∀ z ∈ Metric.closedBall c ρ, AnalyticAt ℂ (Φ F) ↑z) {z : ℍ} (hz : z ∈ Zf F t c ρ) :
    rep Γ c z ∈ Zf F t c ρ := by
  obtain ⟨h, hh, he⟩ := rep_spec (Γ := Γ) c z
  rw [← he]
  exact smul_mem_Zf hF hΓ hnc hA hh hz

theorem Sf_subset_Zf {t : ℂ} {c : ℍ} {ρ : ℝ}
    (hA : ∀ z ∈ Metric.closedBall c ρ, AnalyticAt ℂ (Φ F) ↑z) : Sf Γ F t c ρ ⊆ Zf F t c ρ := by
  intro r hr
  obtain ⟨z, hz, rfl⟩ := mem_Sf.mp hr
  exact rep_mem_Zf hF hΓ hnc hA hz

theorem fibre_finite
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    {ξ : X | 0 < ord F t₀ ξ.out}.Finite :=
  (ModularCurve.finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero_of_finiteIndex Γ F hF hΓ t₀ (hnc t₀)
    hcusp).subset fun ξ hξ => ⟨ξ.out, ne_of_gt hξ, ξ.out_eq⟩

theorem ord_out (t : ℂ) (τ : ℍ) : ord F t (πq τ).out = ord F t τ := by
  obtain ⟨γ, hγ⟩ := Quotient.mk_out (s := MulAction.orbitRel (Γ) ℍ) τ
  rw [← hγ]
  exact ord_smul hΓ γ γ.2 τ

theorem exists_radius (ι : Finset X) (hι : ∀ ξ ∈ ι, 0 < ord F t₀ ξ.out) :
    ∃ ρ > 0,
      (∀ ξ ∈ ι, ∀ z ∈ Metric.closedBall ξ.out ρ, AnalyticAt ℂ (Φ F) ↑z) ∧
      (∀ ξ ∈ ι, ∀ z ∈ Metric.closedBall ξ.out ρ, z ≠ ξ.out →
        Φ F ↑z ≠ t₀ ∧ deriv (Φ F) ↑z ≠ 0) ∧
      (∀ ξ ∈ ι, ∀ γ ∈ Γ, ∀ z ∈ Metric.ball ξ.out ρ, γ • z ∈ Metric.ball ξ.out ρ →
        γ • ξ.out = ξ.out) ∧
      (∀ ξ ∈ ι, ∀ ξ' ∈ ι, ξ ≠ ξ' → ∀ γ ∈ Γ, ∀ z ∈ Metric.ball ξ.out ρ,
        γ • z ∉ Metric.ball ξ'.out ρ) := by
  have han : ∀ ξ ∈ ι, AnalyticAt ℂ (Φ F) ↑ξ.out := fun ξ hξ => Φ_analyticAt hF (hι ξ hξ).le
  have e1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ ι, ∀ z ∈ Metric.closedBall ξ.out ρ,
      AnalyticAt ℂ (Φ F) ↑z :=
    ι.eventually_all.mpr fun ξ hξ =>
      (eventually_closedBall_subset (analyticAt_mem_nhds (han ξ hξ))).mono fun ρ h z hz => h hz
  have e2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ ι, ∀ z ∈ Metric.closedBall ξ.out ρ, z ≠ ξ.out →
      Φ F ↑z ≠ t₀ ∧ deriv (Φ F) ↑z ≠ 0 :=
    ι.eventually_all.mpr fun ξ hξ =>
      (eventually_closedBall_subset (punctured_mem_nhds hF hnc (han ξ hξ) t₀)).mono
        fun ρ h z hz => h hz
  have e3 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ ι, ∀ γ ∈ Γ, ∀ z ∈ Metric.ball ξ.out ρ,
      γ • z ∈ Metric.ball ξ.out ρ → γ • ξ.out = ξ.out :=
    ι.eventually_all.mpr fun ξ _ => by
      obtain ⟨V, hV, hfix⟩ := stab_mem_nhds ξ.out
      exact (eventually_closedBall_subset hV).mono fun ρ h γ _ z hz hγz =>
        hfix γ z (h (Metric.ball_subset_closedBall hz)) (h (Metric.ball_subset_closedBall hγz))
  have e4 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ ι, ∀ ξ' ∈ ι, ξ ≠ ξ' → ∀ γ ∈ Γ,
      ∀ z ∈ Metric.ball ξ.out ρ, γ • z ∉ Metric.ball ξ'.out ρ :=
    ι.eventually_all.mpr fun ξ _ => ι.eventually_all.mpr fun ξ' _ => by
      by_cases hne : ξ = ξ'
      · exact Filter.Eventually.of_forall fun ρ h => (h hne).elim
      · refine (eventually_separated ?_).mono fun ρ h _ => h
        intro γ hγ heq
        apply hne
        have hq : (Quotient.mk _ ξ'.out : X) = Quotient.mk _ ξ.out :=
          Quotient.sound ⟨⟨γ, hγ⟩, heq⟩
        rw [Quotient.out_eq, Quotient.out_eq] at hq
        exact hq.symm
  obtain ⟨ρ, ⟨h1, h2, h3, h4⟩, hρ⟩ :=
    ((e1.and (e2.and (e3.and e4))).and self_mem_nhdsWithin).exists
  exact ⟨ρ, hρ, h1, h2, h3, h4⟩

theorem eventually_fibre_near
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ι : Finset X) (hιall : ∀ τ : ℍ, 0 < ord F t₀ τ → πq τ ∈ ι) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ t in 𝓝 t₀, ∀ τ : ℍ, 0 < ord F t τ →
      ∃ γ ∈ Γ, ∃ ξ ∈ ι, γ • τ ∈ Metric.ball ξ.out ρ := by
  have hU : IsOpen (⋃ ξ ∈ ι, Metric.ball (Quotient.out ξ : ℍ) ρ) :=
    isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have key := UpperHalfPlane.eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos Γ F hF
    hΓ t₀ hcusp hU (fun τ hτ => by
      obtain ⟨γ, hγ⟩ := Quotient.mk_out (s := MulAction.orbitRel (Γ) ℍ) τ
      refine ⟨γ, γ.2, Set.mem_iUnion₂.mpr ⟨πq τ, hιall τ hτ, ?_⟩⟩
      show ((γ • τ : ℍ)) ∈ Metric.ball (Quotient.out (πq τ) : ℍ) ρ
      rw [show γ • τ = (πq τ).out from hγ]
      exact Metric.mem_ball_self hρ)
  refine key.mono fun t ht τ hτ => ?_
  obtain ⟨γ, hγ, hmem⟩ := ht τ hτ
  obtain ⟨ξ, hξ, hz⟩ := Set.mem_iUnion₂.mp hmem
  exact ⟨γ, hγ, ξ, hξ, hz⟩

theorem eventually_ne_cuspValue
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ᶠ t in 𝓝 t₀, ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L) := by
  choose L hL using hcusp
  have hinv : ∀ γ ∈ Γ, ∀ σ, L (γ * σ) = L σ := by
    intro γ hγ σ
    refine tendsto_nhds_unique (hL (γ * σ)).2 ?_
    have : (fun τ : ℍ => F ((γ * σ) • τ)) = fun τ => F (σ • τ) := by
      funext τ; rw [mul_smul, hΓ γ hγ]
    rw [this]; exact (hL σ).2
  have hfin : (Set.range L).Finite := by
    haveI : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
    refine (Set.finite_range fun q : SL(2, ℤ) ⧸ Γ => L (q.out)⁻¹).subset ?_
    rintro _ ⟨σ, rfl⟩
    refine ⟨QuotientGroup.mk σ⁻¹, ?_⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ σ⁻¹
    simp only [hh, mul_inv_rev, inv_inv]
    exact hinv _ (inv_mem h.2) σ
  have hev : ∀ᶠ t in 𝓝 t₀, ∀ x ∈ Set.range L, x ≠ t :=
    hfin.eventually_all.mpr fun x hx => by
      obtain ⟨σ, hσ⟩ := hx
      have hx0 : t₀ ≠ x := hσ ▸ (hL σ).1.symm
      exact (eventually_ne_nhds hx0).mono fun t ht h => ht h.symm
  exact hev.mono fun t ht σ => ⟨L σ, ht _ ⟨σ, rfl⟩, (hL σ).2⟩

section Good

variable {ι : Finset (Quotient (MulAction.orbitRel (Γ) ℍ))} {ρ : ℝ}
  {t : ℂ}

theorem Φ_center (hR : GoodRadius Γ F t₀ ι ρ) {ξ : X} (hξ : ξ ∈ ι) : Φ F ↑ξ.out = t₀ :=
  (ord_pos_iff hF t₀ (hR.R1 ξ hξ _ (Metric.mem_closedBall_self hR.pos.le))).mp (hR.fib ξ hξ)

theorem zero_near (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) (τ : ℍ)
    (hτ : 0 < ord F t τ) : ∃ γ ∈ Γ, ∃ ξ ∈ ι, γ • τ ∈ Zf F t ξ.out ρ := by
  obtain ⟨γ, hγ, ξ, hξ, hz⟩ := ht.near τ hτ
  refine ⟨γ, hγ, ξ, hξ, (mem_Zf_iff_ord_pos hF hΓ hnc (hR.R1 ξ hξ)).mpr
    ⟨Metric.ball_subset_closedBall hz, ?_⟩⟩
  rwa [ord_smul hΓ γ hγ]

theorem Zf_ball (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) {ξ : X} (hξ : ξ ∈ ι)
    {z : ℍ} (hz : z ∈ Zf F t ξ.out ρ) : z ∈ Metric.ball ξ.out ρ := by
  obtain ⟨hzc, hzt⟩ := (mem_Zf hF hΓ hnc (hR.R1 ξ hξ)).mp hz
  rcases eq_or_lt_of_le (Metric.mem_closedBall.mp hzc) with h | h
  · exact absurd hzt (ht.sph ξ hξ z (Metric.mem_sphere.mpr h))
  · exact Metric.mem_ball.mpr h

theorem Zf_ne_center (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) {ξ : X}
    (hξ : ξ ∈ ι) {z : ℍ} (hz : z ∈ Zf F t ξ.out ρ) : z ≠ ξ.out := by
  rintro rfl
  obtain ⟨-, hzt⟩ := (mem_Zf hF hΓ hnc (hR.R1 ξ hξ)).mp hz
  exact ht.ne (hzt.symm.trans (Φ_center hF hΓ hnc hR hξ))

theorem Zf_ord (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) {ξ : X} (hξ : ξ ∈ ι)
    {z : ℍ} (hz : z ∈ Zf F t ξ.out ρ) : ord F t z = 1 := by
  obtain ⟨hzc, hzt⟩ := (mem_Zf hF hΓ hnc (hR.R1 ξ hξ)).mp hz
  exact ord_eq_one hF (hR.R1 ξ hξ z hzc) hzt
    (hR.R2 ξ hξ z hzc (Zf_ne_center hF hΓ hnc hR ht hξ hz)).2

theorem ord_eq_one_of_pos (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) (τ : ℍ)
    (hτ : 0 < ord F t τ) : ord F t τ = 1 := by
  obtain ⟨γ, hγ, ξ, hξ, hz⟩ := zero_near hF hΓ hnc hR ht τ hτ
  rw [← ord_smul hΓ γ hγ τ]
  exact Zf_ord hF hΓ hnc hR ht hξ hz

theorem ord_le_one (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) (τ : ℍ) :
    ord F t τ ≤ 1 := by
  by_cases h : 0 < ord F t τ
  · exact (ord_eq_one_of_pos hF hΓ hnc hR ht τ h).le
  · exact le_trans (not_lt.mp h) zero_le_one

theorem card_eq_two_of_pos (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) (τ : ℍ)
    (hτ : 0 < ord F t τ) : Nat.card (stabilizer Γ′ τ) = 2 :=
  card_stabilizer_eq_two hΓ (ord_eq_one_of_pos hF hΓ hnc hR ht τ hτ)

theorem card_eq_k_of_pos (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) (τ : ℍ)
    (hτ : 0 < ord F t τ) :
    Nat.card (stabilizer Γ τ) = Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ))) :=
  card_stabilizer_eq_k hΓ (ord_eq_one_of_pos hF hΓ hnc hR ht τ hτ)

theorem Sf_inj (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t)
    {ξ : X} (hξ : ξ ∈ ι) {ξ' : X} (hξ' : ξ' ∈ ι)
    {σ : ℍ} (hσ : σ ∈ Sf Γ F t ξ.out ρ) {σ' : ℍ} (hσ' : σ' ∈ Sf Γ F t ξ'.out ρ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (he : γ • σ = σ') : ξ = ξ' ∧ σ = σ' := by
  have hσZ := Sf_subset_Zf hF hΓ hnc (hR.R1 ξ hξ) hσ
  have hσ'Z := Sf_subset_Zf hF hΓ hnc (hR.R1 ξ' hξ') hσ'
  have hb := Zf_ball hF hΓ hnc hR ht hξ hσZ
  have hb' := Zf_ball hF hΓ hnc hR ht hξ' hσ'Z
  have hξξ : ξ = ξ' := by
    by_contra hne
    exact hR.R4 ξ hξ ξ' hξ' hne γ hγ σ hb (he ▸ hb')
  subst hξξ
  refine ⟨rfl, ?_⟩
  have hfix : γ • ξ.out = ξ.out := hR.R3 ξ hξ γ hγ σ hb (he ▸ hb')
  have hstab : (⟨γ, mem_sup_of_mem hγ⟩ : ↥Γ′) ∈ stabilizer Γ′ ξ.out := hfix
  rw [← rep_eq_self_of_mem_Sf hσ, ← rep_eq_self_of_mem_Sf hσ', ← he]
  exact (rep_smul ξ.out σ hstab).symm

theorem exists_mem_Sf (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) (τ : ℍ)
    (hτ : 0 < ord F t τ) : ∃ ξ ∈ ι, ∃ σ ∈ Sf Γ F t ξ.out ρ, ∃ γ ∈ Γ, γ • σ = τ := by
  obtain ⟨γ, hγ, ξ, hξ, hz⟩ := zero_near hF hΓ hnc hR ht τ hτ
  obtain ⟨h, hh, he⟩ := rep_spec (Γ := Γ) ξ.out (γ • τ)
  obtain ⟨g, hg, hgact⟩ := exists_mem_smul_eq (Γ := Γ) h.2
  refine ⟨ξ, hξ, rep Γ ξ.out (γ • τ), mem_Sf.mpr ⟨γ • τ, hz, rfl⟩, (g * γ)⁻¹,
    inv_mem (mul_mem hg hγ), ?_⟩
  rw [← he, hgact, ← mul_smul g γ τ, inv_smul_smul]

theorem sum_Zf_eq (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) {ξ : X}
    (hξ : ξ ∈ ι) (u : ℍ → ℂ)
    (hu : ∀ h ∈ stabilizer Γ′ ξ.out, ∀ z ∈ Zf F t ξ.out ρ, u ((h : SL(2, ℤ)) • z) = u z) :
    ∑ z ∈ Zf F t ξ.out ρ, u z =
      (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ) * ∑ r ∈ Sf Γ F t ξ.out ρ, u r := by
  have h := sum_eq_card_mul_sum_image (G := Γ′) negOne_mem_sup ξ.out (Zf F t ξ.out ρ)
    (fun h hh z hz => smul_mem_Zf hF hΓ hnc (hR.R1 ξ hξ) hh hz)
    (fun z hz => card_eq_two_of_pos hF hΓ hnc hR ht z
      ((mem_Zf_iff_ord_pos hF hΓ hnc (hR.R1 ξ hξ)).mp hz).2) u hu
  rw [h, ModularCurve.orbifoldIndexOf_def]
  rfl

theorem circle_residue (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) {ξ : X}
    (hξ : ξ ∈ ι) (f : CuspForm Γ 2) (c : ℍ → ℂ)
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      f (ofComplex z) / (F (ofComplex z) - t) = c τ / (z - τ) + g z) :
    (∮ z in C(eC ξ.out ρ, eR ξ.out ρ), f (ofComplex z) / (Φ F z - t)) =
      2 * Real.pi * Complex.I * ∑ z ∈ Zf F t ξ.out ρ, c z := by
  classical
  have hA := hR.R1 ξ hξ
  have key := Complex.circleIntegral_eq_sum_residue_of_simplePole (z₀ := eC ξ.out ρ)
    (eR_pos ξ.out hR.pos)
    (fun z => f (ofComplex z) / (Φ F z - t)) (fun a => c (ofComplex a))
    ((Zf F t ξ.out ρ).image ((↑) : ℍ → ℂ)) ?_ ?_ ?_
  · rw [key, Finset.sum_image fun x _ y _ h => UpperHalfPlane.ext h]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ofComplex_apply]
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact coe_mem_ball (Zf_ball hF hΓ hnc hR ht hξ hz)
  · refine forall_closedBall (P := fun w => w ∉ _ → AnalyticAt ℂ _ w) fun z hz hzZ => ?_
    have hzt : Φ F ↑z ≠ t := fun h =>
      hzZ (Finset.mem_image_of_mem _ ((mem_Zf hF hΓ hnc hA).mpr ⟨hz, h⟩))
    exact (cuspForm_analyticAt f z).div ((hA z hz).sub analyticAt_const) (sub_ne_zero.mpr hzt)
  · intro a ha
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨g, hg, hge⟩ := hloc τ
    refine ⟨g, hg, ?_⟩
    filter_upwards [hge, Φ_eventuallyEq hF τ] with z h1 h2
    rw [h2, h1, ofComplex_apply]

theorem sum_circleIntegral_deriv_eq_zero (hR : GoodRadius Γ F t₀ ι ρ)
    (ht : GoodParam Γ F t₀ ι ρ t) (f : CuspForm Γ 2) {E : ℍ → ℂ}
    (hE : ∀ τ : ℍ, HasDerivAt (E ∘ ofComplex) (f τ) ↑τ) :
    ∑ ξ ∈ ι, ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹ *
      ∮ z in C(eC ξ.out ρ, eR ξ.out ρ),
        deriv (fun w : ℂ => E (ofComplex w) - E I) z / (Φ F z - t) = 0 := by
  classical
  obtain ⟨c, hloc, hinv, hsupp, hres⟩ :=
    UpperHalfPlane.exists_residue_cuspForm_div_sub Γ f F hF hΓ t
      (fun τ => ord_le_one hF hΓ hnc hR ht τ) ht.cusp
  have h1 : ∀ ξ ∈ ι,
      (∮ z in C(eC ξ.out ρ, eR ξ.out ρ),
          deriv (fun w : ℂ => E (ofComplex w) - E I) z / (Φ F z - t)) =
        2 * Real.pi * Complex.I *
          ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ) * ∑ r ∈ Sf Γ F t ξ.out ρ, c r) := by
    intro ξ hξ
    rw [← sum_Zf_eq hF hΓ hnc hR ht hξ c (fun h hh z _ => forall_mem_sup hinv _ h.2 z),
      ← circle_residue hF hΓ hnc hR ht hξ f c hloc]
    refine circleIntegral.integral_congr (eR_pos ξ.out hR.pos).le fun w hw => ?_
    exact forall_sphere (P := fun w => deriv (fun w : ℂ => E (ofComplex w) - E I) w /
        (Φ F w - t) = f (ofComplex w) / (Φ F w - t))
      (fun z _ => by
        show deriv (fun w : ℂ => E (ofComplex w) - E I) ↑z / (Φ F ↑z - t) = _
        rw [primitive_deriv f hE (E I) z, ofComplex_apply]) w hw

  set S : Finset ℍ := ι.biUnion fun ξ => Sf Γ F t ξ.out ρ with hS_def
  have hS1 : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ := by
    intro τ hτ
    obtain ⟨ξ, hξ, σ, hσ, γ, hγ, he⟩ := exists_mem_Sf hF hΓ hnc hR ht τ (hsupp τ hτ)
    exact ⟨σ, Finset.mem_biUnion.mpr ⟨ξ, hξ, hσ⟩, γ, hγ, he⟩
  have hS2 : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ' := by
    intro σ hσ σ' hσ' γ hγ he
    obtain ⟨ξ, hξ, hσ⟩ := Finset.mem_biUnion.mp hσ
    obtain ⟨ξ', hξ', hσ'⟩ := Finset.mem_biUnion.mp hσ'
    exact (Sf_inj hF hΓ hnc hR ht hξ hξ' hσ hσ' hγ he).2
  have hdisj : (↑ι : Set X).PairwiseDisjoint fun ξ => Sf Γ F t ξ.out ρ := by
    intro ξ hξ ξ' hξ' hne
    refine Finset.disjoint_left.mpr fun σ hσ hσ' => hne ?_
    exact (Sf_inj hF hΓ hnc hR ht hξ hξ' hσ hσ' (one_mem _) (one_smul _ _)).1
  have hsum0 : ∑ σ ∈ S, c σ = 0 := by
    set k : ℕ := Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ))) with hk
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (k_pos (Γ := Γ)).ne'
    have h3 : ∑ σ ∈ S, c σ = (k : ℂ) * ∑ σ ∈ S, c σ / (Nat.card (stabilizer Γ σ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases hc : c σ = 0
      · simp [hc]
      · rw [card_eq_k_of_pos hF hΓ hnc hR ht σ (hsupp σ hc), ← hk]
        field_simp
    rw [h3, hres S hS1 hS2, mul_zero]
  have h2 : ∑ ξ ∈ ι, ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹ *
      (∮ z in C(eC ξ.out ρ, eR ξ.out ρ),
        deriv (fun w : ℂ => E (ofComplex w) - E I) z / (Φ F z - t)) =
      2 * Real.pi * Complex.I * ∑ ξ ∈ ι, ∑ r ∈ Sf Γ F t ξ.out ρ, c r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    rw [h1 ξ hξ]
    have he : (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (orbifoldIndexOf_pos Γ ξ.out).ne'
    calc ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹ * (2 * Real.pi * Complex.I *
          ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ) * ∑ r ∈ Sf Γ F t ξ.out ρ, c r))
        = 2 * Real.pi * Complex.I * (∑ r ∈ Sf Γ F t ξ.out ρ, c r) *
            (((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹ *
              (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ)) := by ring
      _ = 2 * Real.pi * Complex.I * ∑ r ∈ Sf Γ F t ξ.out ρ, c r := by
            rw [inv_mul_cancel₀ he, mul_one]
  rw [h2, ← Finset.sum_biUnion hdisj, hsum0, mul_zero]

theorem circle_value (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) {ξ : X}
    (hξ : ξ ∈ ι) (f : CuspForm Γ 2) {E : ℍ → ℂ}
    (hE : ∀ τ : ℍ, HasDerivAt (E ∘ ofComplex) (f τ) ↑τ) :
    (∮ z in C(eC ξ.out ρ, eR ξ.out ρ),
        (E (ofComplex z) - E I) * deriv (Φ F) z / (Φ F z - t)) =
      2 * Real.pi * Complex.I * ∑ z ∈ Zf F t ξ.out ρ, (E z - E I) := by
  classical
  have hA := hR.R1 ξ hξ
  have key := circleIntegral_mul_logDeriv_eq (Φ := Φ F) (G := fun w => E (ofComplex w) - E I)
    (eR_pos ξ.out hR.pos) t ((Zf F t ξ.out ρ).image ((↑) : ℍ → ℂ)) ?_ (forall_closedBall hA)
    (forall_closedBall fun z _ => primitive_analyticAt f hE (E I) z) ?_ (fun _ => 1) ?_
  · rw [key, Finset.sum_image fun x _ y _ h => UpperHalfPlane.ext h]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ofComplex_apply, Nat.cast_one, one_mul]
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact coe_mem_ball (Zf_ball hF hΓ hnc hR ht hξ hz)
  · exact forall_closedBall (P := fun w => w ∉ _ → Φ F w ≠ t) fun z hz hzZ h =>
      hzZ (Finset.mem_image_of_mem _ ((mem_Zf hF hΓ hnc hA).mpr ⟨hz, h⟩))
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hzc, -⟩ := (mem_Zf hF hΓ hnc hA).mp hz
    exact analyticOrderAt_eq_of_ord_eq hF hΓ hnc (hA z hzc)
      (by rw [Zf_ord hF hΓ hnc hR ht hξ hz]; rfl)

theorem circle_value₀ (hR : GoodRadius Γ F t₀ ι ρ) {ξ : X} (hξ : ξ ∈ ι) (f : CuspForm Γ 2)
    {E : ℍ → ℂ} (hE : ∀ τ : ℍ, HasDerivAt (E ∘ ofComplex) (f τ) ↑τ) :
    (∮ z in C(eC ξ.out ρ, eR ξ.out ρ),
        (E (ofComplex z) - E I) * deriv (Φ F) z / (Φ F z - t₀)) =
      2 * Real.pi * Complex.I *
        ((ModularCurve.valueMultiplicity F t₀ ξ.out : ℂ) * (E ξ.out - E I)) := by
  classical
  have hA := hR.R1 ξ hξ
  obtain ⟨k, -, hk⟩ := ord_eq_coe_of_pos_of_ne_top (hR.fib ξ hξ) (hnc t₀ ξ.out)
  have hvm : ModularCurve.valueMultiplicity F t₀ ξ.out = k :=
    ModularCurve.valueMultiplicity_of_eq_coe hk
  have key := circleIntegral_mul_logDeriv_eq (Φ := Φ F) (G := fun w => E (ofComplex w) - E I)
    (eR_pos ξ.out hR.pos) t₀ {(ξ.out : ℂ)} ?_ (forall_closedBall hA)
    (forall_closedBall fun z _ => primitive_analyticAt f hE (E I) z) ?_ (fun _ => k) ?_
  · rw [key, Finset.sum_singleton, ofComplex_apply, hvm]
  · intro a ha
    rw [Finset.mem_singleton] at ha
    rw [ha]
    exact coe_mem_ball (Metric.mem_ball_self hR.pos)
  · refine forall_closedBall (P := fun w => w ∉ ({(ξ.out : ℂ)} : Finset ℂ) → Φ F w ≠ t₀)
      fun z hz hzZ => ?_
    have hne : z ≠ ξ.out := fun h => hzZ (by rw [h]; exact Finset.mem_singleton_self _)
    exact (hR.R2 ξ hξ z hz hne).1
  · intro a ha
    rw [Finset.mem_singleton] at ha
    rw [ha]
    exact analyticOrderAt_eq_of_ord_eq hF hΓ hnc (hA _ (Metric.mem_closedBall_self hR.pos.le)) hk

theorem ord_pos_of_valueMultiplicity_ne_zero {t : ℂ} {τ : ℍ}
    (h : ModularCurve.valueMultiplicity F t τ ≠ 0) : 0 < ord F t τ := by
  have hne : ord F t τ ≠ ⊤ := hnc t τ
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  have hv : ModularCurve.valueMultiplicity F t τ = (ord F t τ).untop₀.toNat := rfl
  rw [hv, ← hn, WithTop.untop₀_coe] at h
  rw [← hn]
  have : 0 < n := by
    by_contra h'
    exact h (Int.toNat_eq_zero.mpr (not_lt.mp h'))
  exact_mod_cast this

theorem sum_periodAlong_eq (hR : GoodRadius Γ F t₀ ι ρ) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ s ∈ Metric.ball t₀ ε, s ≠ t₀ → GoodParam Γ F t₀ ι ρ s)
    (ht : t ∈ Metric.ball t₀ ε) (htne : t ≠ t₀) :
    ∑ ξ ∈ ι, ∑ r ∈ Sf Γ F t ξ.out ρ, ModularCurve.periodAlongOf Γ I r =
      ∑ ξ ∈ ι, ((ModularCurve.valueMultiplicity F t₀ ξ.out : ℂ) /
        (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ)) • ModularCurve.periodAlongOf Γ I ξ.out := by
  have htg := hgood t ht htne
  apply LinearMap.ext fun f => ?_
  obtain ⟨E, hE⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ f
  have hE1 : ∀ τ : ℍ, HasDerivAt (E ∘ ofComplex) (f τ) ↑τ := hE.1
  have hT := sum_circleIntegral_eq_of_deriv_eq_zero ι
    (fun ξ => ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹)
    (fun ξ => eC ξ.out ρ) (fun ξ => eR ξ.out ρ) (fun ξ _ => eR_pos ξ.out hR.pos)
    (Φ := Φ F) (G := fun w => E (ofComplex w) - E I) (t₀ := t₀) hε
    (fun ξ hξ => forall_sphere fun z hz => hR.R1 ξ hξ z (Metric.sphere_subset_closedBall hz))
    (fun ξ _ => forall_sphere fun z _ => primitive_analyticAt f hE1 (E I) z)
    (fun s hs ξ hξ => forall_sphere (P := fun w => Φ F w ≠ s) fun z hz => by
      by_cases hs0 : s = t₀
      · rw [hs0]
        have hzc : z ≠ ξ.out := fun h => by
          rw [h, Metric.mem_sphere, dist_self] at hz
          exact hR.pos.ne hz
        exact (hR.R2 ξ hξ z (Metric.sphere_subset_closedBall hz) hzc).1
      · exact (hgood s hs hs0).sph ξ hξ z hz)
    (fun s hs hs0 => sum_circleIntegral_deriv_eq_zero hF hΓ hnc hR (hgood s hs hs0) f hE1) ht

  have hL : ∀ ξ ∈ ι, ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹ *
      (∮ z in C(eC ξ.out ρ, eR ξ.out ρ),
        (E (ofComplex z) - E I) * deriv (Φ F) z / (Φ F z - t)) =
      2 * Real.pi * Complex.I * ∑ r ∈ Sf Γ F t ξ.out ρ, (E r - E I) := by
    intro ξ hξ
    have he : (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (orbifoldIndexOf_pos Γ ξ.out).ne'
    rw [circle_value hF hΓ hnc hR htg hξ f hE1, sum_Zf_eq hF hΓ hnc hR htg hξ (fun z => E z - E I)]
    · calc ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹ * (2 * Real.pi * Complex.I *
            ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ) * ∑ r ∈ Sf Γ F t ξ.out ρ, (E r - E I)))
          = 2 * Real.pi * Complex.I * (∑ r ∈ Sf Γ F t ξ.out ρ, (E r - E I)) *
              (((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹ *
                (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ he, mul_one]
    · intro h hh z _
      obtain ⟨g, hg, hgact⟩ := exists_mem_smul_eq (Γ := Γ) h.2
      have hgc : g • ξ.out = ξ.out := by rw [← hgact]; exact hh
      rw [hgact z, ← periodAlong_eq_sub f hE1 I (g • z), ← periodAlong_eq_sub f hE1 I z,
        periodAlong_smul_of_smul_eq hg hgc z]
  have hR' : ∀ ξ ∈ ι, ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ))⁻¹ *
      (∮ z in C(eC ξ.out ρ, eR ξ.out ρ),
        (E (ofComplex z) - E I) * deriv (Φ F) z / (Φ F z - t₀)) =
      2 * Real.pi * Complex.I *
        ((ModularCurve.valueMultiplicity F t₀ ξ.out : ℂ) /
          (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ) * (E ξ.out - E I)) := by
    intro ξ hξ
    rw [circle_value₀ hF hΓ hnc hR hξ f hE1, div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR', ← Finset.mul_sum, ← Finset.mul_sum]
    at hT
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hT' := mul_left_cancel₀ h2pi hT
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    periodAlong_eq_sub f hE1]
  exact hT'

theorem abelFibreSum_eq₀ (hR : GoodRadius Γ F t₀ ι ρ) :
    ModularCurve.abelFibreSumOf Γ F t₀ =
      ∑ ξ ∈ ι, ((ModularCurve.valueMultiplicity F t₀ ξ.out : ℂ) /
        (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ)) • ModularCurve.periodAlongOf Γ I ξ.out := by
  rw [ModularCurve.abelFibreSumOf_def]
  apply finsum_eq_sum_of_support_subset
  intro ξ hξ
  rw [Function.mem_support] at hξ
  have hvm : ModularCurve.valueMultiplicity F t₀ ξ.out ≠ 0 := by
    intro h; apply hξ; simp [h]
  have := hR.all ξ.out (ord_pos_of_valueMultiplicity_ne_zero hF hΓ hnc hvm)
  rw [Quotient.out_eq] at this
  exact Finset.mem_coe.mpr this

open scoped Classical in

theorem abelFibreSum_eq (hR : GoodRadius Γ F t₀ ι ρ) (ht : GoodParam Γ F t₀ ι ρ t) :
    ModularCurve.abelFibreSumOf Γ F t =
      ∑ σ ∈ ι.biUnion (fun ξ => Sf Γ F t ξ.out ρ), ModularCurve.periodAlongOf Γ I (πq σ).out := by
  classical
  set S : Finset ℍ := ι.biUnion fun ξ => Sf Γ F t ξ.out ρ with hS_def
  have hinj : ∀ x ∈ S, ∀ y ∈ S, πq x = πq y → x = y := by
    intro x hx y hy hxy
    obtain ⟨ξ, hξ, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨ξ', hξ', hy⟩ := Finset.mem_biUnion.mp hy
    have hrel : x ∈ orbit Γ y :=
      orbitRel_apply.mp ((Quotient.eq (r := orbitRel Γ ℍ)).mp hxy)
    obtain ⟨g, hg⟩ := hrel
    exact ((Sf_inj hF hΓ hnc hR ht hξ' hξ hy hx g.2 hg).2).symm
  have hpos_of_mem : ∀ σ ∈ S, 0 < ord F t σ := by
    intro σ hσ
    obtain ⟨ξ, hξ, hσ⟩ := Finset.mem_biUnion.mp hσ
    exact ((mem_Zf_iff_ord_pos hF hΓ hnc (hR.R1 ξ hξ)).mp
      (Sf_subset_Zf hF hΓ hnc (hR.R1 ξ hξ) hσ)).2
  rw [ModularCurve.abelFibreSumOf_def, finsum_eq_sum_of_support_subset _ (s := S.image πq) ?_,
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun σ hσ => ?_
    have hpos : 0 < ord F t (πq σ).out := by
      rw [ord_out hF hΓ hnc]; exact hpos_of_mem σ hσ
    have h1 : ModularCurve.valueMultiplicity F t (πq σ).out = 1 :=
      ModularCurve.valueMultiplicity_of_eq_coe (n := 1)
        (show ord F t (πq σ).out = ((1 : ℕ) : ℤ) by
          rw [ord_eq_one_of_pos hF hΓ hnc hR ht _ hpos]; rfl)
    have h2 : ModularCurve.orbifoldIndexOf Γ (πq σ).out = 1 := by
      rw [ModularCurve.orbifoldIndexOf_def, card_eq_two_of_pos hF hΓ hnc hR ht _ hpos]
    rw [h1, h2, Nat.cast_one, div_one, one_smul]
  · intro ξ' hξ'
    rw [Function.mem_support] at hξ'
    have hvm : ModularCurve.valueMultiplicity F t ξ'.out ≠ 0 := by
      intro h; apply hξ'; simp [h]
    obtain ⟨ξ, hξ, σ, hσ, γ, hγ, he⟩ :=
      exists_mem_Sf hF hΓ hnc hR ht ξ'.out (ord_pos_of_valueMultiplicity_ne_zero hF hΓ hnc hvm)
    rw [Finset.coe_image]
    refine ⟨σ, Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨ξ, hξ, hσ⟩), ?_⟩
    have hout : πq ξ'.out = ξ' := Quotient.out_eq ξ'
    rw [← hout, ← he]
    exact Quotient.sound ⟨⟨γ, hγ⟩⁻¹, inv_smul_smul (⟨γ, hγ⟩ : Γ) σ⟩

theorem sub_mem_of_good (hR : GoodRadius Γ F t₀ ι ρ) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ s ∈ Metric.ball t₀ ε, s ≠ t₀ → GoodParam Γ F t₀ ι ρ s)
    (ht : t ∈ Metric.ball t₀ ε) (htne : t ≠ t₀) :
    ModularCurve.abelFibreSumOf Γ F t - ModularCurve.abelFibreSumOf Γ F t₀ ∈
      ModularCurve.periodLatticeOf Γ := by
  classical
  have htg := hgood t ht htne
  have hdisj : (↑ι : Set X).PairwiseDisjoint fun ξ => Sf Γ F t ξ.out ρ := by
    intro ξ hξ ξ' hξ' hne
    refine Finset.disjoint_left.mpr fun σ hσ hσ' => hne ?_
    exact (Sf_inj hF hΓ hnc hR htg hξ hξ' hσ hσ' (one_mem _) (one_smul _ _)).1
  rw [abelFibreSum_eq hF hΓ hnc hR htg, abelFibreSum_eq₀ hF hΓ hnc hR,
    ← sum_periodAlong_eq hF hΓ hnc hR hε hgood ht htne, ← Finset.sum_biUnion hdisj,
    ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun σ _ => periodAlong_out_sub_mem σ

end Good
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

theorem main
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ᶠ t in 𝓝 t₀,
      ModularCurve.abelFibreSumOf Γ F t - ModularCurve.abelFibreSumOf Γ F t₀ ∈
        ModularCurve.periodLatticeOf Γ := by
  classical
  set ι : Finset X := (fibre_finite hF hΓ hnc hcusp).toFinset with hι_def
  have hι : ∀ ξ ∈ ι, 0 < ord F t₀ ξ.out := fun ξ hξ => by
    simpa [hι_def] using hξ
  have hιall : ∀ τ : ℍ, 0 < ord F t₀ τ → πq τ ∈ ι := fun τ hτ => by
    simp only [hι_def, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rwa [ord_out hF hΓ hnc]
  obtain ⟨ρ, hρ, R1, R2, R3, R4⟩ := exists_radius hF hΓ hnc ι hι
  have hR : GoodRadius Γ F t₀ ι ρ := ⟨hρ, hι, hιall, R1, R2, R3, R4⟩
  have T1 := eventually_fibre_near hF hΓ hnc hcusp ι hιall hρ
  have T2 : ∀ᶠ t in 𝓝 t₀, ∀ ξ ∈ ι, ∀ z ∈ Metric.sphere ξ.out ρ, Φ F ↑z ≠ t := by
    refine (ι.eventually_all).mpr fun ξ hξ => eventually_sphere_ne (R1 ξ hξ) fun z hz => ?_
    have hzc : z ≠ ξ.out := fun h => by
      rw [h, Metric.mem_sphere, dist_self] at hz
      exact hρ.ne hz
    exact (R2 ξ hξ z (Metric.sphere_subset_closedBall hz) hzc).1
  have T3 := eventually_ne_cuspValue hF hΓ hnc hcusp
  obtain ⟨ε, hε, hgood⟩ := Metric.eventually_nhds_iff_ball.mp (T1.and (T2.and T3))
  have hgp : ∀ s ∈ Metric.ball t₀ ε, s ≠ t₀ → GoodParam Γ F t₀ ι ρ s := fun s hs hs0 =>
    ⟨hs0, (hgood s hs).1, (hgood s hs).2.1, (hgood s hs).2.2⟩
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  by_cases htt : t = t₀
  · rw [htt, sub_self]; exact Submodule.zero_mem _
  · exact sub_mem_of_good hF hΓ hnc hR hε hgp ht htt

end Main
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

end ModularCurve.FibreConstOf
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

end
p2m_reactivate "P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.ModularCurve.FibreConstOf.Bridge"

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hnc : ∀ (t : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ᶠ t in 𝓝 t₀,
      ModularCurve.abelFibreSumOf Γ F t - ModularCurve.abelFibreSumOf Γ F t₀ ∈
        ModularCurve.periodLatticeOf Γ :=
  ModularCurve.FibreConstOf.main hF hΓ hnc hcusp

end S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf
end P2MW
export P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf (solution)
