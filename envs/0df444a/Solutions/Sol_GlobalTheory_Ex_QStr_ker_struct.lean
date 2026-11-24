-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.ker_struct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:00.333673+00:00
-- url     : https://prove2.me/submissions/bff9d848-bf55-415a-963c-4737a9fd7b01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_GlobalTheory_Ex_QStr_chr_eq
import Theorems.Thm_GlobalTheory_Ex_QStr_chr_injective
import Theorems.Thm_GlobalTheory_Ex_QStr_split_ext
import Theorems.Thm_GlobalTheory_Ex_QStr_exists_roots
import Theorems.Thm_GlobalTheory_Ex_QStr_root_over
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff
import Theorems.Thm_GlobalTheory_Ex_NumD_tor_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}
namespace GlobalTheory.Ex.QStr
theorem _root_.solution (hk : (k : C) ≠ 0) (a : ℕ)
    (e : (powMonoidHom k : N.A →* N.A).ker ≃* Multiplicative (Fin a → ZMod k)) :
    Nonempty ((powMonoidHom k : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin (a + Module.finrank ℤ N.X) → ZMod k)) := by
  haveI : NeZero k := ⟨by rintro rfl; simp at hk⟩
  obtain ⟨-, -, ε, hε, hε'⟩ := exists_roots C k hk
  let v := Module.finBasis ℤ N.X
  let j : Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) →* (Fin (Module.finrank ℤ N.X) → Cˣ) :=
    MonoidHom.mk' (fun y i => ε (Multiplicative.ofAdd (y.toAdd i))) fun y y' => funext fun i => by
      simp [ofAdd_add]
  have hj : Function.Injective j := fun y y' h => by
    refine Multiplicative.toAdd.injective (funext fun i => ?_)
    exact Multiplicative.ofAdd.injective (hε (congrFun h i))
  let i₀ := N.torHom.comp ((chr v).comp j)
  have hpow : ∀ y, i₀ y ∈ (powMonoidHom k : N.Gt →* N.Gt).ker := fun y => by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    have : y ^ k = 1 := by
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      simp
    rw [this, map_one]
  let π₀ : (powMonoidHom k : N.Gt →* N.Gt).ker →* (powMonoidHom k : N.A →* N.A).ker :=
    (N.projB.comp (Subgroup.subtype _)).codRestrict _ fun g => by
      have h : g.1 ^ k = 1 := g.2
      change g.1.b ^ k = 1
      rw [← NumD.Gt.pow_b, h, NumD.Gt.one_b]
  refine split_ext k a _ (fun x => Subtype.ext x.2) (i₀.codRestrict _ hpow) (e.toMonoidHom.comp π₀) ?_ ?_ ?_
  · intro y y' h
    exact hj (chr_injective v (N.tor_injective (congrArg Subtype.val h)))
  · intro z
    obtain ⟨b, rfl⟩ := e.surjective z
    obtain ⟨γ, h, h'⟩ := root_over N (NeZero.ne k) 1 b.1 b.2
    exact ⟨⟨γ, h'⟩, congrArg e (Subtype.ext h)⟩
  · intro x
    constructor
    · intro h
      have h1 : π₀ x = 1 := e.injective (h.trans (map_one e).symm)
      obtain ⟨t, ht⟩ := (N.exists_tor_iff x.1).2 (congrArg Subtype.val h1)
      have h2 : t ^ k = 1 := N.tor_injective (by rw [N.tor_pow, ht, N.tor_one]; exact x.2)
      choose z hz using fun i => hε' (t (Multiplicative.ofAdd (v i))) (DFunLike.congr_fun h2 _)
      refine ⟨Multiplicative.ofAdd fun i => (z i).toAdd, Subtype.ext ?_⟩
      change N.tor (chr v _) = x.1
      rw [← ht, ← chr_eq v t]
      congr 2
      exact funext hz
    · rintro ⟨y, rfl⟩
      exact (congrArg e (Subtype.ext rfl)).trans (map_one e)
end GlobalTheory.Ex.QStr
