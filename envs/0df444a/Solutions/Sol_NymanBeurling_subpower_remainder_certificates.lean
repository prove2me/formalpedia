-- Prove2me | solution 1 for NymanBeurling.subpower_remainder_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:59:59.117736+00:00
-- url     : https://prove2.me/submissions/75169c50-ec3c-41ff-9f87-8778df5941ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_polynomial_cutoff_rational_gram_criterion
import Theorems.Thm_NymanBeurling_cofinal_subcubic_rational_gram_rows

open Finset NymanBeurling.RationalGram
namespace SubcubicCertificate

private theorem budget {n J : ℕ} (hn : 2 ≤ n)
    (hg : gap (n^(J+2)) (512*n^(3*(J+1))) ≤ 1/(J+1:ℚ)) :
    ∃ c : ℕ →₀ ℚ, headEnergy c (512*n^(3*(J+1))) ≤ 1/(J+1:ℚ) ∧
      (cost c (512*n^(3*(J+1))))^(J+1) ≤ ((512*n^(3*(J+1)):ℕ)+1:ℚ) := by
  let D := n^(J+2)
  let H := 512*n^(3*(J+1))
  have dn : n ≤ D := Nat.le_self_pow (by omega) _
  have dH : D ≤ n^(3*(J+1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hH : D+1 ≤ H := by dsimp [H];omega
  have hD : (2:ℚ) ≤ D := by exact_mod_cast hn.trans dn
  have hp : (2:ℚ) ≤ n := by exact_mod_cast hn
  have hg' : gap D H ≤ 1 := by
    exact hg.trans (by apply div_le_one_of_le₀ <;> have := (Nat.cast_nonneg J : (0:ℚ) ≤ J) <;> linarith)
  have hgram := (NymanBeurling.polynomial_cutoff_rational_gram_criterion.2.1 D H hH)
  obtain ⟨c,_,he,hc⟩ := hgram.2.2.2
  refine ⟨c,he.le.trans hg,?_⟩
  have hm : 2*(D+2:ℚ)^2+36*(D+1:ℚ)^3*gap D H ≤ 296*(D:ℚ)^3 := by
    calc
      _ ≤ 2*(2*D:ℚ)^2+36*(2*D:ℚ)^3*1 := by gcongr <;> linarith
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (D:ℚ)) (show 0 ≤ (D:ℚ)-1 by linarith)]
  have hfactor : (D:ℚ)^3=(n:ℚ)^3*(n:ℚ)^(3*(J+1)) := by
    dsimp [D];push_cast
    rw [←pow_mul,←pow_add];congr 1;omega
  have hh : (H:ℚ)=512*(n:ℚ)^(3*(J+1)) := by dsimp [H];push_cast;rfl
  have hden : 0 < (n:ℚ)^(3*(J+1)) := by positivity
  have ht : (2*(D+2:ℚ)^2+36*(D+1:ℚ)^3*gap D H)/(H+1:ℚ) ≤ 296*(n:ℚ)^3/512 := by
    calc
      _ ≤ 296*(D:ℚ)^3/(H+1:ℚ) := by gcongr
      _ ≤ 296*(D:ℚ)^3/(H:ℚ) := by apply div_le_div_of_nonneg_left (by positivity) (by rw [hh];positivity);linarith
      _ = _ := by rw [hfactor,hh];field_simp
  have hn3 : (8:ℚ) ≤ (n:ℚ)^3 := by
    calc
      8=(2:ℚ)^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp 3
  have hcost : cost c H ≤ (n:ℚ)^3 := by linarith only [hc,hg',ht,hn3]
  have hpos : 0 ≤ cost c H := by unfold cost headEnergy;positivity
  calc
    (cost c H)^(J+1) ≤ ((n:ℚ)^3)^(J+1) := pow_le_pow_left₀ hpos hcost _
    _ ≤ (H+1:ℚ) := by rw [←pow_mul,hh];linarith
end SubcubicCertificate

theorem solution (J L : ℕ) :
  ∃ (H K : ℕ) (c : ℕ→₀ℚ), L≤H ∧ (
    let R := fun n : ℕ => 1-∑ k∈c.support,c k*((((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))
    let E := fun n : ℕ => ((R n)^2/((n+1:ℚ)*(n+2:ℚ)):ℚ)
    let C : ℚ := (∑ n∈Finset.range K,E n)+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ)
    (∑ n∈Finset.range H,E n)≤1/(J+1:ℚ) ∧ C^(J+1)≤(H+1:ℚ))  := by
  obtain ⟨n,hn,hg⟩ := NymanBeurling.cofinal_subcubic_rational_gram_rows J L
  have hn' := (le_max_left 2 L).trans hn
  obtain ⟨c,hp,hc⟩ := SubcubicCertificate.budget hn' hg
  let H := 512*n^(3*(J+1))
  have hL : L ≤ H := calc
    L ≤ n := (le_max_right 2 L).trans hn
    _ ≤ n^(3*(J+1)) := Nat.le_self_pow (by omega) _
    _ ≤ H := by dsimp [H];omega
  refine ⟨H,H,c,hL,?_⟩
  simpa only [H, NymanBeurling.RationalGram.cost,headEnergy,NymanBeurling.RationalGram.residual,mass,
    Nat.cast_add,Nat.cast_ofNat,mul_div_assoc] using And.intro hp hc
