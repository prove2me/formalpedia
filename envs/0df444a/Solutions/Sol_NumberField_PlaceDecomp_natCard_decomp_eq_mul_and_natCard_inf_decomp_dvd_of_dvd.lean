-- Prove2me | solution 1 for NumberField.PlaceDecomp.natCard_decomp_eq_mul_and_natCard_inf_decomp_dvd_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/89461b2f-155e-52f2-95fc-52f7fe27bc89

import Mathlib
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_natCard_decomp_eq_mul_and_natCard_inf_decomp_dvd_of_dvd
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "NumberField P2MW.S_NumberField_PlaceDecomp_natCard_decomp_eq_mul_and_natCard_inf_decomp_dvd_of_dvd.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_natCard_decomp_eq_mul_and_natCard_inf_decomp_dvd_of_dvd.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "mk PlaceDecomp.exists_restrict_decomp_surjective_of_tower PlaceDecomp.decomp"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "exists_restrict_decomp_surjective_of_tower decomp"
namespace DegreeDvd
p2m_open "NumberField.PlaceDecomp NumberField"

variable {E K M : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra E K] [Algebra E M] [Algebra K M] [IsScalarTower E K M] [IsGalois E K] [IsGalois E M]

omit [NumberField E] [NumberField K] [NumberField M] [IsScalarTower E K M] [IsGalois E K] [IsGalois E M] in

theorem mem_iff_forall_apply_algebraMap
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (K ≃ₐ[E] K))
    (hι : ∀ (g : M ≃ₐ[E] M) (y : K), algebraMap K M (ι (QuotientGroup.mk g) y) = g (algebraMap K M y))
    (g : M ≃ₐ[E] M) : g ∈ S ↔ ∀ y : K, g (algebraMap K M y) = algebraMap K M y := by
  constructor
  · intro hg y
    rw [← hι g y, (QuotientGroup.eq_one_iff g).2 hg, map_one, AlgEquiv.one_apply]
  · intro hg
    rw [← QuotientGroup.eq_one_iff, ← MulEquiv.map_eq_one_iff ι]
    ext y
    apply (algebraMap K M).injective
    rw [hι, hg, AlgEquiv.one_apply]

theorem natCard_decomp_eq
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (K ≃ₐ[E] K))
    (hι : ∀ (g : M ≃ₐ[E] M) (y : K), algebraMap K M (ι (QuotientGroup.mk g) y) = g (algebraMap K M y))
    (W : HeightOneSpectrum (𝓞 M)) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) =
      Nat.card ↥(S ⊓ NumberField.PlaceDecomp.decomp E M W) * Nat.card ↥(NumberField.PlaceDecomp.decomp E K (W.under (𝓞 K))) := by
  obtain ⟨r, hsurj, -, hker, -⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E K M W

  have h1 : Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) = Nat.card r.ker * r.ker.index :=
    (Subgroup.card_mul_index r.ker).symm
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top] at h1
  rw [h1]
  congr 1

  refine Nat.card_congr
    { toFun := fun σ => ⟨((σ : ↥(NumberField.PlaceDecomp.decomp E M W)) : M ≃ₐ[E] M),
        ⟨(mem_iff_forall_apply_algebraMap S ι hι _).2 ((hker _).1 σ.2), (σ : ↥(NumberField.PlaceDecomp.decomp E M W)).2⟩⟩
      invFun := fun g => ⟨⟨(g : M ≃ₐ[E] M), g.2.2⟩, (hker _).2 ((mem_iff_forall_apply_algebraMap S ι hι _).1 g.2.1)⟩
      left_inv := fun σ => rfl
      right_inv := fun g => rfl }

end NumberField.PlaceDecomp.DegreeDvd

theorem solution
    (E F L M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra E F] [Algebra E L] [Algebra E M] [Algebra F M] [Algebra L M]
    [IsScalarTower E F M] [IsScalarTower E L M] [IsGalois E F] [IsGalois E L] [IsGalois E M]
    (SF : Subgroup (M ≃ₐ[E] M)) [SF.Normal] (ιF : (M ≃ₐ[E] M) ⧸ SF ≃* (F ≃ₐ[E] F))
    (hιF : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ιF (QuotientGroup.mk g) x) = g (algebraMap F M x))
    (SL : Subgroup (M ≃ₐ[E] M)) [SL.Normal] (ιL : (M ≃ₐ[E] M) ⧸ SL ≃* (L ≃ₐ[E] L))
    (hιL : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ιL (QuotientGroup.mk g) y) = g (algebraMap L M y))
    (W : HeightOneSpectrum (𝓞 M))
    (hdvd : Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ∣
      Nat.card ↥(NumberField.PlaceDecomp.decomp E L (W.under (𝓞 L)))) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) =
        Nat.card ↥(SF ⊓ NumberField.PlaceDecomp.decomp E M W) * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ∧
      Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) =
        Nat.card ↥(SL ⊓ NumberField.PlaceDecomp.decomp E M W) * Nat.card ↥(NumberField.PlaceDecomp.decomp E L (W.under (𝓞 L))) ∧
      Nat.card ↥(SL ⊓ NumberField.PlaceDecomp.decomp E M W) ∣ Nat.card ↥(SF ⊓ NumberField.PlaceDecomp.decomp E M W) := by
  have hF := NumberField.PlaceDecomp.DegreeDvd.natCard_decomp_eq (K := F) SF ιF hιF W
  have hL := NumberField.PlaceDecomp.DegreeDvd.natCard_decomp_eq (K := L) SL ιL hιL W
  refine ⟨hF, hL, ?_⟩
  obtain ⟨t, ht⟩ := hdvd
  have hpos : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := Nat.card_pos
  refine ⟨t, ?_⟩
  have : Nat.card ↥(SF ⊓ NumberField.PlaceDecomp.decomp E M W) * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) =
      Nat.card ↥(SL ⊓ NumberField.PlaceDecomp.decomp E M W) * t * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := by
    rw [← hF, hL, ht]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end S_NumberField_PlaceDecomp_natCard_decomp_eq_mul_and_natCard_inf_decomp_dvd_of_dvd
end P2MW
export P2MW.S_NumberField_PlaceDecomp_natCard_decomp_eq_mul_and_natCard_inf_decomp_dvd_of_dvd (solution)
