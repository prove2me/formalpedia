-- Prove2me | solution 1 for GlobalTheory.LevelFibre.trivAt_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:22.481049+00:00
-- url     : https://prove2.me/submissions/cb04bce0-b2aa-4f5f-a3b4-8715dc86bd44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
import Theorems.Thm_GlobalTheory_LevelFibre_sub_eq_one
import Theorems.Thm_GlobalTheory_LevelFibre_modN_of_ev_eq
import Theorems.Thm_GlobalTheory_LevelFibre_mem_of_eq_one
import Theorems.Thm_GlobalTheory_LevelFibre_sub_mem_of_inGam
import Theorems.Thm_GlobalTheory_LevelFibre_unit_left
import Theorems.Thm_GlobalTheory_LevelFibre_sec_w
import Theorems.Thm_GlobalTheory_LevelFibre_exists_ptEquiv
import Theorems.Thm_GlobalTheory_LevelFibre_sab_cast
import Theorems.Thm_GlobalTheory_LevelFibre_exists_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabComp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}
namespace GlobalTheory.LevelFibre
theorem _root_.solution
    (hPull : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo.X), ∃ o' : Obj D l (baseKA l) (z ≫ Xo.s), Nonempty (ObjMap o' Xo.univ z))
    (hRig : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo.X) (o' : Obj D l (baseKA l) (z ≫ Xo.s)) (m m' : SABMap o'.t Xo.univ.t z),
      (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo₂.X) (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X) (hg : g.InGam l l₂)
    (hρ : Xo₂.LevAut g ρ) (hx : x ≫ ρ.hom = x) : g.TrivAt l₂ := by
  obtain ⟨-, ν, hν, hνA⟩ := hρ
  obtain ⟨o, ⟨p⟩⟩ := hPull k (x ≫ r)
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ r x m p.toSABMap
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν n
  obtain ⟨n₃, hn₃⟩ := sab_cast hx n₂
  obtain ⟨n₄, hn₄⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n₃
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart x _ rfl
  obtain ⟨eν, heν⟩ := exists_ptEquiv ν.cart x x hx
  let P : D.La → (Over.mk x ⟶ Xo₂.univ.t.G) := fun a => toUnit _ ≫ Xo₂.univ.eta a
  let PA : D.La → (Over.mk x ⟶ Xo₂.univ.t.G) := fun a => toUnit _ ≫ Xo₂.univ.etaA a
  have hP : ∀ a b, P (a + b) = P a * P b := fun a b => by
    simp only [P]; rw [Xo₂.univ.eta_add, MonObj.comp_mul]
  have hPpow : ∀ a, (P a ^ (l₂.M / l.M)).left = x ≫ (Xo₂.univ.eta a ^ (l₂.M / l.M)).left := fun a => by
    simp only [P]; rw [← MonObj.comp_pow, unit_left]
  have hPe : ∀ a, e (P a ^ (l₂.M / l.M)) = toUnit _ ≫ Xo.univ.eta a := fun a => by
    apply Over.OverMorphism.ext
    rw [he, hPpow, unit_left, Category.assoc, Category.assoc]
    exact congrArg _ (hm a)
  have hPν : ∀ a, eν (P (g.f l₂.M a)) = P a := fun a => by
    apply Over.OverMorphism.ext
    simp only [P]
    rw [heν, unit_left, unit_left, Category.assoc]
    exact (congrArg _ (hν a)).trans (by rw [← Category.assoc, hx])
  have hPAν : ∀ a, eν (PA (g.f l₂.A a)) = PA a := fun a => by
    apply Over.OverMorphism.ext
    simp only [PA]
    rw [heν, unit_left, unit_left, Category.assoc]
    exact (congrArg _ (hνA a)).trans (by rw [← Category.assoc, hx])
  have hfix : ∀ a, eν (P a ^ (l₂.M / l.M)) = P a ^ (l₂.M / l.M) := fun a => by
    have h : P (g.f l₂.M a) ^ (l₂.M / l.M) = P a ^ (l₂.M / l.M) := by
      apply e.injective
      rw [hPe, hPe, ← sub_add_cancel (g.f l₂.M a) a, Xo.univ.eta_add, Xo.univ.eta_ker _ (sub_mem_of_inGam hd hg a),
        _root_.one_mul]
    rw [← h, map_pow, hPν, h]
  have hon : ∀ a, (o.eta a).left ≫ n.φ = (P a ^ (l₂.M / l.M)).left := fun a => by
    apply m.cart.1.hom_ext
    · rw [← he, hPe, unit_left, Category.assoc]
      exact (congrArg _ hn.symm).trans (p.eta a)
    · rw [Over.w, Category.assoc, n.cart.1.w, ← Category.assoc, sec_w]; exact (Category.id_comp x).symm
  have hrig : p.toSABMap.φ = n₄.φ := hRig k _ o p.toSABMap n₄ fun a => ⟨_, rfl, by
    rw [hn₄, hn₃, hn₂, hn, ← Category.assoc, ← Category.assoc, ← Category.assoc, hon, ← heν, hfix]⟩
  have hnν : n.φ ≫ ν.φ = n.φ := by
    rw [← hn₂, ← hn₃]
    apply m.cart.1.hom_ext
    · exact hn₄.symm.trans (hrig.symm.trans hn)
    · exact n₃.cart.1.w.trans n.cart.1.w.symm
  have hid : ∀ q, eν q = q := fun q => by
    apply Over.OverMorphism.ext
    have hq : n.cart.1.lift q.left (𝟙 _) ((Over.w q).trans (Category.id_comp x).symm) ≫ n.φ = q.left :=
      n.cart.1.lift_fst _ _ _
    rw [heν, ← hq, Category.assoc]
    exact congrArg _ hnν
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Xo₂.s)
  obtain ⟨-, I, -, hIA, hI⟩ := Xo₂.univ.geom k x β hβ
  refine ⟨fun a => mem_of_eq_one l₂ I P hP (fun b hb => ?_) hI (sub_eq_one P hP ?_), fun a => ?_⟩
  · simp only [P]; rw [Xo₂.univ.eta_ker b hb, MonObj.comp_one]
  · rw [← hPν a, hid]
  · apply modN_of_ev_eq I l₂.A_pos
    rw [← hIA, ← hIA]
    exact (hid _).symm.trans (hPAν a)
end GlobalTheory.LevelFibre
