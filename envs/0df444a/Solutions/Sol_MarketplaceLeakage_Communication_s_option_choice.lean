-- Prove2me | solution 1 for MarketplaceLeakage.Communication.s_option_choice
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T08:36:49.765319+00:00
-- url     : https://prove2.me/submissions/074803da-b282-4ba6-9c44-1eaf61f3ac4d

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting
open MarketplaceLeakage.Communication

theorem solution(v c : ℝ) (hvc : c < v) (q η f : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    lowPay v c q η f < highPay v c q η f ↔ (1 - (2 - q) * η) * q * v / (1 - η) - c < f := by
  have h1 : 0 < 1 - η := by linarith
  unfold lowPay highPay
  rw [sub_lt_iff_lt_add, div_lt_iff₀ h1]
  constructor <;> intro h <;> nlinarith [h]
